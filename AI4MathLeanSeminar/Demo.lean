import Mathlib

/-
# Lean4 入门讲义
目标：建立对 Lean 的直觉感受，认识基本关键词与 Infoview 界面
-/

-- ============================================================
-- § 0  动机：素数无限定理
-- ============================================================

/-
证明思路：对任意 n，令 N = n! + 1。
设 p 为 N 的最小素因子，则 p 是素数。
若 p ≤ n，则 p ∣ n!，又 p ∣ N = n! + 1，故 p ∣ 1，矛盾。
因此 p > n。
-/
theorem infinite_primes (n : ℕ) : ∃ p, p.Prime ∧ p > n := by
  -- 构造 N = n! + 1
  let N := n.factorial + 1
  -- 取 N 的最小素因子 p
  let p := N.minFac
  -- 声明存在这个 p
  use p
  -- 证明 p 是素数（minFac 保证，前提是 N ≠ 1）
  have hp : p.Prime := by
    apply Nat.minFac_prime
    have h1 : n.factorial ≥ 1 := Nat.factorial_pos n
    omega
  refine ⟨hp, ?_⟩
  -- 反证：假设 p ≤ n
  by_contra hle
  -- p ≤ n 且 p 是素数，故 p ∣ n!
  have h_p_dvd_fac : p ∣ n.factorial :=
    Nat.dvd_factorial hp.pos (Nat.not_lt.mp hle)
  -- p 是 N 的因子，故 p ∣ n! + 1
  have h_p_dvd_N : p ∣ N := Nat.minFac_dvd N
  -- p ∣ n! 且 p ∣ n! + 1，故 p ∣ 1
  have h_p_dvd_one : p ∣ 1 :=
    (Nat.dvd_add_iff_right h_p_dvd_fac).mpr h_p_dvd_N
  -- 素数不整除 1，矛盾
  exact hp.not_dvd_one h_p_dvd_one

-- ============================================================
-- § 1  一切都有类型
-- ============================================================

/-
Lean 最核心的直觉：任何表达式都有唯一的类型。
输出形式 `A : B` 读作"A 的类型是 B"。
  `:` 左边是项（term），右边是类型（type）
  `:=` 读作"定义为"，右边给出具体的值
-/

-- 用 #check 查看类型
#check 1
#check (1 : ℝ)
#check Real.sqrt 2

-- 函数也有类型
def f (x : ℕ) := x + 3
#check f        -- f : ℕ → ℕ

-- 类型也有类型？
#check Nat
#check Type

-- def 名字 : 类型 := 值
def myNumber : Nat := 42
def double (n : Nat) : Nat := n * 2

-- #check 查看名字的类型（不求值）
#check myNumber    -- myNumber : ℕ
#check double   -- double : ℕ → ℕ
#check Real.sqrt 2  -- Real.sqrt 2 : ℝ

-- #eval 求值
#eval double 5   -- 10

-- ============================================================
-- § 2  命题是 Prop，证明是项
-- ============================================================

/-
命题在 Lean 中同样是表达式，类型是 Prop。
-/

#check 2 + 2 = 4           -- Prop
#check ∀ n : ℕ, n + 0 = n  -- Prop

def myFermatLastTheorem : Prop :=
  ∀ x y z n : ℕ, n > 2 ∧ x * y * z ≠ 0 → x ^ n + y ^ n ≠ z ^ n

#check myFermatLastTheorem  -- Prop

/-
如果 P : Prop，那么"P 的证明"就是一个类型为 P 的项。
证明的类型就是它所证明的命题。
-/

theorem easy : 2 + 2 = 4 := rfl
#check easy   -- easy : 2 + 2 = 4

-- sorry 是占位符，表示"暂时承认"，正式提交时应避免
theorem hard : myFermatLastTheorem := sorry
#check hard   -- hard : myFermatLastTheorem

/-
小结：Lean 里"数学对象 / 命题 / 证明"统一成"项 + 类型"的语言。
-/

-- ============================================================
-- § 3  定理的骨架
-- ============================================================

/-
模板：theorem 名称 参数/假设 : 目标 := by 证明
  - theorem   关键字，声明这是一个定理
  - 参数/假设  说明在什么条件下成立
  - : 目标    要证明的结论（定理的类型就是它的结论）
  - := by     从这里开始写 tactic 证明
-/

-- 把光标放在每行 tactic 上，观察右侧 Infoview 中目标的变化
theorem The_first_example {G : Type*} [Group G] {a b c d e f : G}
    (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  exact mul_assoc c d f

/-
光标停在 rw [h'] 之后，Infoview 显示：

  G : Type u_1
  inst✝ : Group G
  a b c d e f : G
  h : a * b = c * d
  h' : e = f
  ⊢ a * (b * f) = c * (d * f)

⊢ 上方是当前可用的假设，⊢ 右边是当前目标。
随着证明推进，目标逐步被改写，直到出现 No goals。
-/

-- ============================================================
-- § 4  常用 tactic 速览
-- ============================================================

-- ── 1. 改写（rw / calc）────────────────────────────────────

-- rw [h]：用等式 h 把目标中的左边替换成右边
-- 目标前：⊢ a * (b * e) = c * (d * f)
-- rw [h'] 后：⊢ a * (b * f) = c * (d * f)
example (a b : ℝ) (h : a = b) : a + 1 = b + 1 := by
  rw [h]

-- calc：分步等式链，每行 _ 代表上一行右边
example (a b c : ℝ) (h1 : a = b) (h2 : b = c) : a = c := by
  calc a = b := h1
       _ = c := h2

-- ── 2. 运用定理（exact / apply）────────────────────────────

-- exact e：目标恰好是 e 的类型，直接关闭
example (p : Prop) (h : p) : p := by
  exact h

-- apply f：目标匹配 f 的结论，剩余前提变为新子目标
-- 目标前：⊢ 2 ≤ 4
-- apply Nat.le_of_succ_le 后：⊢ 2 + 1 ≤ 4
example (p q : Prop) (hpq : p → q) (hp : p) : q := by
  apply hpq
  exact hp

-- ── 3. 逻辑（constructor / intro / obtain）─────────────────

-- constructor：把 ⊢ P ∧ Q 拆成两个子目标 ⊢ P 和 ⊢ Q
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  · exact hp
  · exact hq

-- intro：把 ⊢ P → Q 中的 P 移入假设，目标变为 ⊢ Q
example (p q : Prop) (h : p → q) : p → q := by
  intro hp
  exact h hp

-- obtain：拆解假设（∧、∃ 等）
example (p q : Prop) (h : p ∧ q) : q := by
  obtain ⟨_, hq⟩ := h
  exact hq

-- ── 4. 自动化（rfl / ring / omega / simp / linarith）───────

-- rfl：两边定义相等时直接关闭
example : 2 + 3 = 5 := by rfl

-- ring：任意加减乘的代数恒等式
example (a b : ℝ) : (a + b)^2 = a^2 + 2*a*b + b^2 := by ring

-- omega：整数/自然数线性算术
example (n : ℕ) (h : n > 3) : n ≥ 4 := by omega

-- linarith：实数线性不等式
example (x y : ℝ) (h1 : x > 1) (h2 : y > 1) : x + y > 2 := by linarith

-- simp：化简（调用一组引理）
example : 5 + 0 = 5 := by simp

-- ============================================================
-- § 5  练习
-- ============================================================

-- 练习 1：定义 triple，返回 n * 3
def triple (n : Nat) : Nat := sorry
-- #eval triple 4   -- 期望输出 12

-- 练习 2：证明 3 + 4 = 7
theorem ex2 : 3 + 4 = 7 := by
  sorry

-- 练习 3：证明 10 + 0 = 10
theorem ex3 : 10 + 0 = 10 := by
  sorry

-- 练习 4：从 p 和 q 推出 q
theorem proj2 (p q : Prop) (hp : p) (hq : q) : q := by
  sorry

-- 练习 5：用 ring 证明
example (a b : ℝ) : (a + b) * (a - b) = a^2 - b^2 := by
  sorry
