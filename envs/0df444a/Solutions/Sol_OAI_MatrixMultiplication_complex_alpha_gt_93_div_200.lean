-- Prove2me | solution 1 for OAI.MatrixMultiplication.complex_alpha_gt_93_div_200
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T18:27:06.619676+00:00
-- url     : https://prove2.me/submissions/7217d4cd-6a31-4706-b603-c455f9dab223

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Sum
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Semicontinuity.Basic
import Std
import Definitions.Def_MatrixMultiplication
import Definitions.Def_Q235MM002

section
-- module Solutions.Q235_MM.MatrixMultiplication_Arithmetic_Complexity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Division-free arithmetic programs over a field and their operation counts. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic

namespace MatrixAlgorithm

variable {F : Type*} [Field F] {a b c : ℕ}

theorem correct_iff_entries (P : MatrixAlgorithm F a b c) :
    P.Correct ↔ ∀ (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin b) (Fin c) F)
      (i : Fin a) (k : Fin c),
      P.program.eval (matrixInputs A B) (P.output i k) = ∑ j, A i j * B j k := by
  constructor
  · intro h A B i k
    exact congrFun (congrFun (h A B) i) k
  · intro h A B
    funext i k
    exact h A B i k

end MatrixAlgorithm

theorem scalarAlgorithm_correct (F : Type*) [Field F] : (scalarAlgorithm F).Correct := by
  intro A B
  funext i k
  have hi : i = 0 := Subsingleton.elim _ _
  have hk : k = 0 := Subsingleton.elim _ _
  subst i
  subst k
  change A 0 0 * B 0 0 = (A * B) 0 0
  simp [Matrix.mul_apply]

theorem one_le_innerSize {n : ℕ} (hn : 1 ≤ n) (k : ℝ) : 1 ≤ innerSize n k := by
  apply Nat.one_le_ceil_iff.mpr
  exact Real.rpow_pos_of_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)) k

theorem innerSize_mono {n : ℕ} (hn : 1 ≤ n) {k l : ℝ} (hkl : k ≤ l) :
    innerSize n k ≤ innerSize n l := by
  exact Nat.ceil_mono (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hkl)

theorem innerSize_le_pow {a b n t : ℕ} {k : ℝ} (hk : 0 ≤ k)
    (hn : n ≤ a ^ t) (hab : (a : ℝ) ^ k ≤ b) : innerSize n k ≤ b ^ t := by
  apply Nat.ceil_le.mpr
  calc
    (n : ℝ) ^ k ≤ ((a ^ t : ℕ) : ℝ) ^ k :=
      Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hn) hk
    _ = ((a : ℝ) ^ k) ^ t := by
      rw [Nat.cast_pow, ← Real.rpow_pow_comm (Nat.cast_nonneg a)]
    _ ≤ (b : ℝ) ^ t := pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg a) k) hab t
    _ = ((b ^ t : ℕ) : ℝ) := by rw [Nat.cast_pow]

theorem innerSize_cast_le {n : ℕ} (hn : 1 ≤ n) {k : ℝ} (hk : 0 ≤ k) :
    (innerSize n k : ℝ) ≤ 2 * (n : ℝ) ^ k := by
  have hpow : 1 ≤ (n : ℝ) ^ k := Real.one_le_rpow (by exact_mod_cast hn) hk
  have hceil := (Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg n) k)).le
  change (⌈(n : ℝ) ^ k⌉₊ : ℝ) ≤ _
  linarith

end MatrixMultiplication.Arithmetic

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Arithmetic_LowerBound
attribute [-simp] _root_.OAI.MatrixMultiplication.Arithmetic.Gate.cost_mapInput _root_.OAI.MatrixMultiplication.Arithmetic.Gate.cost_mapRegister _root_.OAI.MatrixMultiplication.Arithmetic.Gate.cost_mapSource _root_.OAI.MatrixMultiplication.Arithmetic.Gate.eval_mapInput _root_.OAI.MatrixMultiplication.Arithmetic.Gate.eval_mapSource _root_.OAI.MatrixMultiplication.Arithmetic.MatrixAlgorithm.pad_cost_eq _root_.OAI.MatrixMultiplication.Arithmetic.Program.cost_append _root_.OAI.MatrixMultiplication.Arithmetic.Program.cost_mapInput _root_.OAI.MatrixMultiplication.Arithmetic.Program.cost_mapSource _root_.OAI.MatrixMultiplication.Arithmetic.Program.eval_mapInput _root_.OAI.MatrixMultiplication.Arithmetic.Program.eval_mapSource _root_.OAI.MatrixMultiplication.Arithmetic.RecursiveBlock.Family.cost_ofMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Division-free arithmetic programs over a field and their operation counts. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic

namespace Program

variable {F Input : Type*}

theorem sum_registerCost {r : ℕ} (p : Program F Input r) :
    ∑ i, p.registerCost i = p.cost := by
  induction p with
  | nil => simp [registerCost, cost]
  | step p g ih => simp [registerCost, Fin.sum_univ_succ, ih, Nat.add_comm]

theorem eval_eq_constant_or_input_of_registerCost_eq_zero [Field F]
    {r : ℕ} (p : Program F Input r) (i : Fin r) (hi : p.registerCost i = 0) :
    (∃ z : F, ∀ inputs, p.eval inputs i = z) ∨
      (∃ a : Input, ∀ inputs, p.eval inputs i = inputs a) := by
  revert i
  induction p with
  | nil => intro i; exact Fin.elim0 i
  | @step r p g ih =>
    intro i hi
    revert hi
    refine Fin.cases ?_ (fun j => ?_) i
    · intro hi
      change g.cost = 0 at hi
      cases g with
      | constant z => exact Or.inl ⟨z, fun _ => rfl⟩
      | input a => exact Or.inr ⟨a, fun _ => rfl⟩
      | add a b => simp [Gate.cost] at hi
      | sub a b => simp [Gate.cost] at hi
      | mul a b => simp [Gate.cost] at hi
    · intro hi
      simpa only [eval_step_succ] using ih j hi

end Program

section ElementaryMatrices

variable {F : Type*} [Field F] {a b c : ℕ}

theorem elementaryProduct (i x : Fin a) (j : Fin b) (k z : Fin c) :
    (elementaryLeft (F := F) i j * elementaryRight (F := F) j k) x z =
      if (x, z) = (i, k) then 1 else 0 := by
  by_cases hi : x = i <;> by_cases hk : z = k <;>
    simp [Matrix.mul_apply, elementaryLeft, elementaryRight, hi, hk]

end ElementaryMatrices

namespace MatrixAlgorithm

variable {F : Type*} [Field F] {a b c : ℕ}

theorem output_injective (P : MatrixAlgorithm F a b c) (hb : 1 ≤ b)
    (hP : P.Correct) : Function.Injective (fun o : Fin a × Fin c => P.output o.1 o.2) := by
  classical
  intro x y hxy
  change P.output x.1 x.2 = P.output y.1 y.2 at hxy
  let j : Fin b := ⟨0, by omega⟩
  let A := elementaryLeft (F := F) x.1 j
  let B := elementaryRight (F := F) j x.2
  have hx := congrFun (congrFun (hP A B) x.1) x.2
  have hy := congrFun (congrFun (hP A B) y.1) y.2
  have heq : (A * B) x.1 x.2 = (A * B) y.1 y.2 := by
    rw [← hx, ← hy]
    change P.program.eval (matrixInputs A B) (P.output x.1 x.2) =
      P.program.eval (matrixInputs A B) (P.output y.1 y.2)
    rw [hxy]
  simp only [A, B, elementaryProduct, Prod.eta, ite_true, if_true] at heq
  by_contra hne
  have hyx : y ≠ x := Ne.symm hne
  simp [hyx] at heq

theorem one_le_output_registerCost (P : MatrixAlgorithm F a b c) (hb : 1 ≤ b)
    (hP : P.Correct) (i : Fin a) (k : Fin c) :
    1 ≤ P.program.registerCost (P.output i k) := by
  by_contra hn
  have hzero : P.program.registerCost (P.output i k) = 0 := by omega
  let j : Fin b := ⟨0, by omega⟩
  have hentry (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin b) (Fin c) F) :
      P.program.eval (matrixInputs A B) (P.output i k) = (A * B) i k :=
    congrFun (congrFun (hP A B) i) k
  rcases P.program.eval_eq_constant_or_input_of_registerCost_eq_zero
      (P.output i k) hzero with ⟨z, hz⟩ | ⟨u, hu⟩
  · have hz0 : z = 0 := by
      have h := hentry 0 0
      rw [hz] at h
      simpa using h
    have hz1 : z = 1 := by
      have h := hentry (elementaryLeft i j) (elementaryRight j k)
      rw [hz] at h
      simpa only [elementaryProduct, ite_true, if_true] using h
    exact (zero_ne_one : (0 : F) ≠ 1) (hz0.symm.trans hz1)
  · rcases u with ⟨x, y⟩ | ⟨y, z⟩
    · have h := hentry (Matrix.of fun _ _ => 1) 0
      rw [hu] at h
      simp [matrixInputs, Matrix.mul_apply] at h
    · have h := hentry 0 (Matrix.of fun _ _ => 1)
      rw [hu] at h
      simp [matrixInputs, Matrix.mul_apply] at h

theorem output_size_le_cost (P : MatrixAlgorithm F a b c) (hb : 1 ≤ b)
    (hP : P.Correct) : a * c ≤ P.cost := by
  classical
  let f : Fin a × Fin c → Fin P.registers := fun o => P.output o.1 o.2
  have hf : Function.Injective f := P.output_injective hb hP
  calc
    a * c = ∑ _o : Fin a × Fin c, (1 : ℕ) := by simp
    _ ≤ ∑ o : Fin a × Fin c, P.program.registerCost (f o) := by
      apply Finset.sum_le_sum
      intro o ho
      exact P.one_le_output_registerCost hb hP o.1 o.2
    _ = ∑ r ∈ Finset.univ.image f, P.program.registerCost r := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => hf h
    _ ≤ ∑ r, P.program.registerCost r :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = P.cost := P.program.sum_registerCost

end MatrixAlgorithm

theorem rectangularAdmissibleExponent_two_le {F : Type*} [Field F] {k τ : ℝ}
    (hτ : RectangularAdmissibleExponent F k τ) : 2 ≤ τ := by
  by_contra hneg
  have hτlt : τ < 2 := lt_of_not_ge hneg
  let ε : ℝ := (2 - τ) / 2
  have hε : 0 < ε := by dsimp [ε] <;> linarith
  obtain ⟨C, hC, hbound⟩ := hτ ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (max (C ^ ε⁻¹) 1)
  have hnreal : 1 < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  have hnpos : 0 < (n : ℝ) := lt_trans zero_lt_one hnreal
  have hn1 : 1 ≤ n := (Nat.one_le_cast (α := ℝ)).mp hnreal.le
  have hpow : C < (n : ℝ) ^ ε :=
    (Real.rpow_inv_lt_iff_of_pos hC.le (Nat.cast_nonneg n) hε).mp
      (lt_of_le_of_lt (le_max_left _ _) hn)
  obtain ⟨P, hP, hcost⟩ := hbound n hn1
  have hlower : (n : ℝ) ^ (2 : ℕ) ≤ P.cost := by
    have h : n ^ 2 ≤ P.cost := by
      simpa [pow_two] using P.output_size_le_cost (one_le_innerSize hn1 k) hP
    exact_mod_cast h
  have hstrict : (n : ℝ) ^ (2 : ℕ) < (n : ℝ) ^ (2 : ℕ) := calc
    (n : ℝ) ^ (2 : ℕ) ≤ C * (n : ℝ) ^ (τ + ε) := hlower.trans hcost
    _ < (n : ℝ) ^ ε * (n : ℝ) ^ (τ + ε) :=
      mul_lt_mul_of_pos_right hpow (Real.rpow_pos_of_pos hnpos _)
    _ = (n : ℝ) ^ (2 : ℕ) := by
      rw [← Real.rpow_add hnpos]
      have he : ε + (τ + ε) = 2 := by dsimp [ε] <;> ring
      rw [he]
      norm_num
  exact (lt_irrefl _ hstrict)

theorem rectangularAdmissibleExponent_bddBelow (F : Type*) [Field F] (k : ℝ) :
    BddBelow {τ : ℝ | RectangularAdmissibleExponent F k τ} :=
  ⟨2, fun _ h => rectangularAdmissibleExponent_two_le h⟩

theorem rectangularOmega_le_of_admissibleExponent {F : Type*} [Field F] {k τ : ℝ}
    (hτ : RectangularAdmissibleExponent F k τ) : rectangularOmega F k ≤ τ :=
  csInf_le (rectangularAdmissibleExponent_bddBelow F k) hτ

end MatrixMultiplication.Arithmetic

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Arithmetic_NaiveAlgorithm
attribute [-simp] _root_.OAI.MatrixMultiplication.Arithmetic.MatrixAlgorithm.pad_cost_eq _root_.OAI.MatrixMultiplication.Arithmetic.Program.cost_mapInput _root_.OAI.MatrixMultiplication.Arithmetic.Program.cost_mapSource _root_.OAI.MatrixMultiplication.Arithmetic.RecursiveBlock.Family.cost_ofMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Division-free arithmetic programs over a field and their operation counts. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic

variable {F : Type*} [Field F]

namespace Expression

variable {Input : Type*}

theorem sumFin_eval {n : ℕ} (f : Fin n → Expression F Input) (inputs : Input → F) :
    (sumFin f).eval inputs = ∑ i, (f i).eval inputs := by
  induction n with
  | zero => simp [sumFin, eval]
  | succ n ih => simp [sumFin, eval, ih, Fin.sum_univ_succ]

theorem sumFin_cost {n : ℕ} (f : Fin n → Expression F Input) :
    (sumFin f).cost = (∑ i, (f i).cost) + n := by
  induction n with
  | zero => simp [sumFin, cost]
  | succ n ih =>
    simp only [sumFin, cost, ih, Fin.sum_univ_succ]
    omega

end Expression

theorem naiveEntry_eval {a b c : ℕ} (i : Fin a) (k : Fin c)
    (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin b) (Fin c) F) :
    (naiveEntry i k).eval (matrixInputs A B) = ∑ j, A i j * B j k := by
  simp [naiveEntry, Expression.sumFin_eval, Expression.eval, matrixInputs]

@[simp] theorem naiveEntry_cost {a b c : ℕ} (i : Fin a) (k : Fin c) :
    (naiveEntry (F := F) (b := b) i k).cost = 2 * b := by
  simp [naiveEntry, Expression.sumFin_cost, Expression.cost, two_mul]

theorem naiveAlgorithm_correct (a b c : ℕ) : (naiveAlgorithm (F := F) a b c).Correct := by
  apply (MatrixAlgorithm.correct_iff_entries _).2
  intro A B i k
  let p := Expression.compileFamily (fun ik : Fin a × Fin c => naiveEntry (F := F) (b := b) ik.1 ik.2)
  change p.program.eval (matrixInputs A B) (p.output (i, k)) = _
  rw [p.correct]
  exact naiveEntry_eval i k A B

@[simp] theorem naiveAlgorithm_cost (a b c : ℕ) :
    (naiveAlgorithm (F := F) a b c).cost = 2 * a * b * c := by
  let p := Expression.compileFamily (fun ik : Fin a × Fin c => naiveEntry (F := F) (b := b) ik.1 ik.2)
  change p.program.cost = _
  rw [p.cost_eq]
  simp only [naiveEntry_cost, Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  ring

end MatrixMultiplication.Arithmetic

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Arithmetic_Padding
attribute [-simp] _root_.OAI.MatrixMultiplication.Arithmetic.RecursiveBlock.Family.cost_ofMatrix _root_.OAI.MatrixMultiplication.Arithmetic.naiveEntry_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Division-free arithmetic programs over a field and their operation counts. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic

variable {F : Type*} [Field F]

theorem sum_fin_castLE_of_zero {n m : ℕ} (h : n ≤ m) (f : Fin m → F)
    (hf : ∀ j : Fin m, n ≤ j.val → f j = 0) :
    (∑ j : Fin m, f j) = ∑ j : Fin n, f (Fin.castLE h j) := by
  symm
  refine Fintype.sum_of_injective (Fin.castLE h) ?_
    (fun j : Fin n => f (Fin.castLE h j)) f ?_ (fun _ => rfl)
  · intro i j hij
    exact Fin.ext (congrArg (fun v : Fin m => v.val) hij)
  · intro j hj
    exact hf j (le_of_not_gt fun hsmall => hj ⟨⟨j.val, hsmall⟩, Fin.ext rfl⟩)

theorem zeroPadMatrix_mul {a b c A B C : ℕ} (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C)
    (M : Matrix (Fin a) (Fin b) F) (N : Matrix (Fin b) (Fin c) F)
    (i : Fin a) (k : Fin c) :
    (zeroPadMatrix A B M * zeroPadMatrix B C N) (Fin.castLE ha i) (Fin.castLE hc k) =
      (M * N) i k := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  calc
    (∑ j : Fin B,
        zeroPadMatrix A B M (Fin.castLE ha i) j *
          zeroPadMatrix B C N j (Fin.castLE hc k)) =
        ∑ j : Fin b,
          zeroPadMatrix A B M (Fin.castLE ha i) (Fin.castLE hb j) *
            zeroPadMatrix B C N (Fin.castLE hb j) (Fin.castLE hc k) := by
      apply sum_fin_castLE_of_zero hb
      intro j hj
      simp [zeroPadMatrix, not_lt_of_ge hj]
    _ = ∑ j : Fin b, M i j * N j k := by simp

theorem padSource_eval {a b c A B C : ℕ}
    (M : Matrix (Fin a) (Fin b) F) (N : Matrix (Fin b) (Fin c) F) :
    (fun x : MatrixInput A B C => Sum.elim (matrixInputs M N) id (padSource x)) =
      matrixInputs (zeroPadMatrix A B M) (zeroPadMatrix B C N) := by
  funext x
  rcases x with ⟨i, j⟩ | ⟨j, k⟩
  · by_cases hi : i.val < a <;> by_cases hj : j.val < b <;>
      simp [padSource, matrixInputs, zeroPadMatrix, hi, hj]
  · by_cases hj : j.val < b <;> by_cases hk : k.val < c <;>
      simp [padSource, matrixInputs, zeroPadMatrix, hj, hk]

namespace MatrixAlgorithm

theorem pad_correct {a b c A B C : ℕ} (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C)
    {P : MatrixAlgorithm F A B C} (hP : P.Correct) : (pad ha hb hc P).Correct := by
  intro M N
  funext i k
  change (P.program.mapSource (padSource (a := a) (b := b) (c := c))).eval
    (matrixInputs M N) (P.output (Fin.castLE ha i) (Fin.castLE hc k)) = (M * N) i k
  rw [Program.eval_mapSource, padSource_eval]
  have hentry := congrFun (congrFun
    (hP (zeroPadMatrix A B M) (zeroPadMatrix B C N)) (Fin.castLE ha i)) (Fin.castLE hc k)
  exact hentry.trans (zeroPadMatrix_mul ha hb hc M N i k)

theorem exists_restrict {a b c A B C : ℕ} (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C)
    (P : MatrixAlgorithm F A B C) (hP : P.Correct) :
    ∃ Q : MatrixAlgorithm F a b c, Q.Correct ∧ Q.cost ≤ P.cost :=
  ⟨pad ha hb hc P, pad_correct ha hb hc hP, (pad_cost_eq ha hb hc P).le⟩

end MatrixAlgorithm

end MatrixMultiplication.Arithmetic

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Arithmetic_Exponent
attribute [-simp] _root_.OAI.MatrixMultiplication.Arithmetic.RecursiveBlock.Family.cost_ofMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Division-free arithmetic programs over a field and their operation counts. -/

noncomputable section

namespace MatrixMultiplication.Arithmetic

variable {F : Type*} [Field F]

theorem rectangularAdmissibleExponent_of_uniform_costs {k τ C : ℝ} (hC : 0 < C)
    (hbound : ∀ n : ℕ, 1 ≤ n → ∃ P : MatrixAlgorithm F n (innerSize n k) n,
      P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ τ) :
    RectangularAdmissibleExponent F k τ := by
  intro ε hε
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨P, hP, hcost⟩ := hbound n hn
  refine ⟨P, hP, hcost.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
    (le_add_of_nonneg_right hε.le)

theorem rectangularAdmissibleExponent_naive (k : ℝ) :
    RectangularAdmissibleExponent F k (2 + max k 0) := by
  apply rectangularAdmissibleExponent_of_uniform_costs (C := 4) (by norm_num)
  intro n hn
  refine ⟨naiveAlgorithm n (innerSize n k) n,
    naiveAlgorithm_correct n (innerSize n k) n, ?_⟩
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hinner : (innerSize n k : ℝ) ≤ 2 * (n : ℝ) ^ max k 0 :=
    (Nat.cast_le.mpr (innerSize_mono hn (le_max_left k 0))).trans
      (innerSize_cast_le hn (le_max_right k 0))
  rw [naiveAlgorithm_cost]
  push_cast
  calc
    2 * (n : ℝ) * innerSize n k * n = 2 * (n : ℝ) ^ 2 * innerSize n k := by ring
    _ ≤ 2 * (n : ℝ) ^ 2 * (2 * (n : ℝ) ^ max k 0) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = 4 * (n : ℝ) ^ (2 + max k 0) := by
      rw [Real.rpow_add hnpos]
      norm_num
      ring

theorem rectangularAdmissibleExponent_nonempty (k : ℝ) :
    Set.Nonempty {τ : ℝ | RectangularAdmissibleExponent F k τ} :=
  ⟨2 + max k 0, rectangularAdmissibleExponent_naive k⟩

theorem rectangularOmega_two_le (k : ℝ) : 2 ≤ rectangularOmega F k :=
  le_csInf (rectangularAdmissibleExponent_nonempty k)
    (fun _ hτ => rectangularAdmissibleExponent_two_le hτ)

@[simp] theorem rectangularOmega_zero : rectangularOmega F 0 = 2 := by
  apply le_antisymm _ (rectangularOmega_two_le 0)
  apply rectangularOmega_le_of_admissibleExponent
  simpa using (rectangularAdmissibleExponent_naive (F := F) 0)

theorem complexAlpha_set_bddAbove :
    BddAbove {k : ℝ | k ∈ Set.Icc 0 1 ∧ rectangularOmega ℂ k = 2} :=
  ⟨1, fun _ h => h.1.2⟩

theorem le_complexAlpha {k : ℝ} (hk : k ∈ Set.Icc 0 1)
    (hω : rectangularOmega ℂ k = 2) : k ≤ complexAlpha :=
  le_csSup complexAlpha_set_bddAbove ⟨hk, hω⟩

end MatrixMultiplication.Arithmetic

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Tensor_ComplexTensorBatching
attribute [-simp] _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_auxiliaryRank _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_columns _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_inner _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_multiplicity _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_occurrences _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_rows _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_inner _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_multiplicity _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_outer _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_rank _root_.OAI.MatrixMultiplication.Foundation.CW75InitialExecution.execution_value _root_.OAI.MatrixMultiplication.Foundation.CW75Primitive.restriction_basePolynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.boundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.boundary_basePolynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.cyclicBoundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.twiceCyclicBoundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.ExecutionPairingBudget.MatrixCoordinates.scalar_tensor _root_.OAI.MatrixMultiplication.Foundation.ExecutionPairingBudget.MatrixCoordinates.standard_tensor _root_.OAI.MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution.cyclic_auxiliary _root_.OAI.MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution.onSupport_auxiliary _root_.OAI.MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution.onSupport_value _root_.OAI.MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution.reindexOriginal_auxiliary _root_.OAI.MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution.reindexOutput_auxiliary _root_.OAI.MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution.step_auxiliary _root_.OAI.MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution.swapXY_auxiliary _root_.OAI.MatrixMultiplication.Foundation.PolynomialLocalConstruction.kernel_constantMatrix_coeff_zero _root_.OAI.MatrixMultiplication.Foundation.PolynomialLocalConstruction.kernel_weightedCoordinatePolynomialMatrix_coeff_zero _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.cyclic_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.ofRankAtMost_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.product_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.pullback_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.restrict_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialRestrictionDegeneration.compose_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.restrictPolynomial_coeff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {K X Y Z U V W : Type*} [CommSemiring K]

theorem diagonal_rankAtMost (ι : Type*) [Fintype ι] [DecidableEq ι] :
    RankAtMost (diagonal (K := K) ι) (Fintype.card ι) := by
  let a : ι → ι → K := fun i j => if i = j then 1 else 0
  have heq : diagonal (K := K) ι =
      fun x y z => ∑ i, rankOne (a i) (a i) (a i) x y z := by
    funext x y z
    simp [diagonal, rankOne, a, mul_ite, ite_and]
    split_ifs <;> simp_all
  rw [heq]
  exact rankAtMost_sum_rankOne a a a

theorem RankAtMost.repeat_batch {S : Tensor K U V W} {k r R B : ℕ}
    (hbatch : RankAtMost (directSum (fun _ : Fin k => S)) r) (hfit : R ≤ B * k) :
    RankAtMost (directSum (fun _ : Fin R => S)) (B * r) := by
  classical
  let f : Fin R → Fin B × Fin k := fun i => finProdFinEquiv.symm (Fin.castLE hfit i)
  have hf : Function.Injective f := finProdFinEquiv.symm.injective.comp (Fin.castLE_injective hfit)
  have hbig := (diagonal_rankAtMost (K := K) (Fin B)).product hbatch
  simp only [Fintype.card_fin] at hbig
  rcases hbig with ⟨a, b, c, heq⟩
  let liftU : (Fin R × U) → Fin B × (Fin k × U) := fun x => ((f x.1).1, (f x.1).2, x.2)
  let liftV : (Fin R × V) → Fin B × (Fin k × V) := fun y => ((f y.1).1, (f y.1).2, y.2)
  let liftW : (Fin R × W) → Fin B × (Fin k × W) := fun z => ((f z.1).1, (f z.1).2, z.2)
  refine ⟨fun i x => a i (liftU x), fun i y => b i (liftV y),
    fun i z => c i (liftW z), ?_⟩
  funext x y z
  change directSum (fun _ : Fin R => S) x y z =
    ∑ i, rankOne (a i) (b i) (c i) (liftU x) (liftV y) (liftW z)
  have hentry := congrFun (congrFun (congrFun heq (liftU x)) (liftV y)) (liftW z)
  rw [← hentry]
  by_cases hxy : x.1 = y.1
  · by_cases hxz : x.1 = z.1
    · have hyz : y.1 = z.1 := hxy.symm.trans hxz
      simp [directSum, Tensor.product, diagonal, liftU, liftV, liftW, hxy, hyz]
    · have hn : f x.1 ≠ f z.1 := fun h => hxz (hf h)
      have hs : (f x.1).1 ≠ (f z.1).1 ∨ (f x.1).2 ≠ (f z.1).2 := by
        by_cases hfirst : (f x.1).1 = (f z.1).1
        · exact Or.inr (fun hsecond => hn (Prod.ext hfirst hsecond))
        · exact Or.inl hfirst
      rcases hs with hs | hs <;>
        simp [directSum, Tensor.product, diagonal, liftU, liftV, liftW, hxz, hs]
  · have hn : f x.1 ≠ f y.1 := fun h => hxy (hf h)
    have hs : (f x.1).1 ≠ (f y.1).1 ∨ (f x.1).2 ≠ (f y.1).2 := by
      by_cases hfirst : (f x.1).1 = (f y.1).1
      · exact Or.inr (fun hsecond => hn (Prod.ext hfirst hsecond))
      · exact Or.inl hfirst
    rcases hs with hs | hs <;>
      simp [directSum, Tensor.product, diagonal, liftU, liftV, liftW, hxy, hs]

theorem RankAtMost.batch_substitute [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor K X Y Z} {S : Tensor K U V W} {r b : ℕ}
    (hT : RankAtMost T r)
    (hbatch : RankAtMost (directSum (fun _ : Fin r => S)) b) :
    RankAtMost (Tensor.product T S) b := by
  classical
  rcases hT with ⟨a, c, e, rfl⟩
  let A : (X × U) → (Fin r × U) → K :=
    fun x i => if x.2 = i.2 then a i.1 x.1 else 0
  let B : (Y × V) → (Fin r × V) → K :=
    fun y i => if y.2 = i.2 then c i.1 y.1 else 0
  let C : (Z × W) → (Fin r × W) → K :=
    fun z i => if z.2 = i.2 then e i.1 z.1 else 0
  have heq : Tensor.restrict A B C (directSum (fun _ : Fin r => S)) =
      Tensor.product (fun x y z => ∑ i, rankOne (a i) (c i) (e i) x y z) S := by
    funext x y z
    simp [Tensor.restrict, directSum, Tensor.product, rankOne, A, B, C,
      Fintype.sum_prod_type, ite_and, ite_mul, mul_ite, Finset.sum_mul]
  rw [← heq]
  exact hbatch.restrict A B C

theorem RankAtMost.batch_product [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor K X Y Z} {S : Tensor K U V W} {R k r B : ℕ}
    (hT : RankAtMost T R)
    (hbatch : RankAtMost (directSum (fun _ : Fin k => S)) r)
    (hfit : R ≤ B * k) : RankAtMost (Tensor.product T S) (B * r) :=
  hT.batch_substitute (hbatch.repeat_batch hfit)

end Tensor
end MatrixMultiplication.Foundation

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Tensor_ComplexMatrixTensor
attribute [-simp] _root_.OAI.MatrixMultiplication.Foundation.ExecutionPairingBudget.MatrixCoordinates.standard_tensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {K A B C D E F : Type*} [CommSemiring K]

theorem contract_matrixCoefficients [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (left : A × B → K) (right : B × C → K) (i : A) (k : C) :
    contract (matrixCoefficients A B C) left right (k, i) =
      ∑ j, left (i, j) * right (j, k) := by
  simp [contract, matrixCoefficients, Fintype.sum_prod_type, ite_and, ite_mul]

theorem matrixCoefficients_cyclic [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (x : B × C) (y : C × A) (z : A × B) :
    matrixCoefficients (K := K) A B C z x y = matrixCoefficients B C A x y z := by
  have h : (z.2 = x.1 ∧ x.2 = y.1 ∧ y.2 = z.1) ↔
      (x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1) :=
    ⟨fun h => ⟨h.2.1, h.2.2, h.1⟩, fun h => ⟨h.2.2, h.1, h.2.1⟩⟩
  simp only [matrixCoefficients, h]

theorem matrixCoefficients_rank_of_product [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq D] [DecidableEq E] [DecidableEq F] {r : ℕ}
    (hproduct : RankAtMost (product (matrixCoefficients (K := K) A B C)
      (matrixCoefficients D E F)) r) :
    RankAtMost (matrixCoefficients (K := K) (A × D) (B × E) (C × F)) r := by
  have h := hproduct.pullback
    (fun x : (A × D) × (B × E) => ((x.1.1, x.2.1), (x.1.2, x.2.2)))
    (fun y : (B × E) × (C × F) => ((y.1.1, y.2.1), (y.1.2, y.2.2)))
    (fun z : (C × F) × (A × D) => ((z.1.1, z.2.1), (z.1.2, z.2.2)))
  have heq : pullback
      (fun x : (A × D) × (B × E) => ((x.1.1, x.2.1), (x.1.2, x.2.2)))
      (fun y : (B × E) × (C × F) => ((y.1.1, y.2.1), (y.1.2, y.2.2)))
      (fun z : (C × F) × (A × D) => ((z.1.1, z.2.1), (z.1.2, z.2.2)))
      (product (matrixCoefficients (K := K) A B C) (matrixCoefficients D E F)) =
      matrixCoefficients (K := K) (A × D) (B × E) (C × F) := by
    funext x y z
    exact matrixCoefficients_product x y z
  rw [heq] at h
  exact h

theorem matrixCoefficients_power [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (n : ℕ) (x : (Fin n → A) × (Fin n → B))
    (y : (Fin n → B) × (Fin n → C)) (z : (Fin n → C) × (Fin n → A)) :
    Tensor.power (matrixCoefficients (K := K) A B C) n
      (fun i => (x.1 i, x.2 i)) (fun i => (y.1 i, y.2 i)) (fun i => (z.1 i, z.2 i)) =
      matrixCoefficients (Fin n → A) (Fin n → B) (Fin n → C) x y z := by
  simp only [Tensor.power, matrixCoefficients, Fintype.prod_boole, forall_and, ← funext_iff]

end Tensor
end MatrixMultiplication.Foundation

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Arithmetic_RecursiveBlockPrograms
attribute [-simp] _root_.OAI.MatrixMultiplication.Arithmetic.naiveEntry_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Division-free arithmetic programs over a field and their operation counts. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic.RecursiveBlock

open MatrixMultiplication.Foundation

variable {F : Type*} [Field F]

namespace LinearExpression

variable {Input : Type*}

theorem eval_sumFin (n : ℕ) (f : Fin n → Expression F Input) (inputs : Input → F) :
    (sumFin n f).eval inputs = ∑ i, (f i).eval inputs := by
  induction n with
  | zero => simp [sumFin, Expression.eval]
  | succ n ih =>
    simp only [sumFin, Expression.eval, ih, Fin.sum_univ_succ]

theorem cost_sumFin (n : ℕ) (f : Fin n → Expression F Input) :
    (sumFin n f).cost = (∑ i, (f i).cost) + n := by
  induction n with
  | zero => simp [sumFin, Expression.cost]
  | succ n ih =>
    simp only [sumFin, Expression.cost, ih, Fin.sum_univ_succ]
    omega

theorem eval_linear {Term : Type*} [Fintype Term]
    (a : Term → F) (wire : Term → Input) (inputs : Input → F) :
    (linear a wire).eval inputs = ∑ i, a i * inputs (wire i) := by
  rw [linear, eval_sumFin]
  exact (Fintype.equivFin Term).symm.sum_comp (fun i => a i * inputs (wire i))

theorem cost_linear {Term : Type*} [Fintype Term]
    (a : Term → F) (wire : Term → Input) :
    (linear a wire).cost = 2 * Fintype.card Term := by
  simp [linear, cost_sumFin, Expression.cost, two_mul]

end LinearExpression

namespace Family

variable {Input Mid Output : Type*}

theorem eval_expressions [Fintype Output] (e : Output → Expression F Input)
    (inputs : Input → F) (o : Output) :
    (expressions e).eval inputs o = (e o).eval inputs :=
  (Expression.compileFamily e).correct inputs o

theorem cost_expressions [Fintype Output] (e : Output → Expression F Input) :
    (expressions e).cost = ∑ o, (e o).cost :=
  (Expression.compileFamily e).cost_eq

theorem eval_compose (p : Family F Input Mid) (q : Family F Mid Output)
    (inputs : Input → F) (o : Output) :
    (compose p q).eval inputs o = q.eval (p.eval inputs) o :=
  (p.program.substitute q.program p.output).correct inputs (q.output o)

theorem cost_compose (p : Family F Input Mid) (q : Family F Mid Output) :
    (compose p q).cost = p.cost + q.cost :=
  (p.program.substitute q.program p.output).cost_eq

theorem eval_mapInputs {NewInput : Type*} (f : Input → NewInput)
    (p : Family F Input Output) (inputs : NewInput → F) (o : Output) :
    (p.mapInputs f).eval inputs o = p.eval (fun i => inputs (f i)) o := by
  exact Program.eval_mapInput f p.program inputs (p.output o)

omit [Field F] in
theorem cost_mapInputs {NewInput : Type*} (f : Input → NewInput)
    (p : Family F Input Output) : (p.mapInputs f).cost = p.cost := by
  exact Program.cost_mapInput f p.program

theorem eval_parallel (r : ℕ) (p : Fin r → Family F Input Output)
    (inputs : Input → F) (o : Fin r × Output) :
    (parallel r p).eval inputs o = (p o.1).eval inputs o.2 := by
  induction r with
  | zero => exact Fin.elim0 o.1
  | succ r ih =>
    rcases o with ⟨i, o⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Program.eval_append_old _ _ inputs _
    · exact (Program.eval_append_new _ _ inputs _).trans
        (ih (fun j => p j.succ) (j, o))

omit [Field F] in
theorem cost_parallel (r : ℕ) (p : Fin r → Family F Input Output) :
    (parallel r p).cost = ∑ i, (p i).cost := by
  induction r with
  | zero => simp [parallel, cost, Program.cost]
  | succ r ih =>
    change ((p 0).program.append (parallel r (fun i => p i.succ)).program).cost = _
    rw [Program.cost_append]
    change (p 0).cost + (parallel r (fun i => p i.succ)).cost = _
    rw [ih, Fin.sum_univ_succ]

theorem eval_copies (r : ℕ) (p : Family F Input Output)
    (inputs : Fin r × Input → F) (o : Fin r × Output) :
    (copies r p).eval inputs o = p.eval (fun x => inputs (o.1, x)) o.2 := by
  rw [copies, eval_parallel, eval_mapInputs]

omit [Field F] in
theorem cost_copies (r : ℕ) (p : Family F Input Output) :
    (copies r p).cost = r * p.cost := by
  simp [copies, cost_parallel, cost_mapInputs]

theorem eval_ofMatrix {m l q : ℕ} (p : MatrixAlgorithm F m l q) (hp : p.Correct)
    (inputs : MatrixInput m l q → F) (o : Fin m × Fin q) :
    (ofMatrix p).eval inputs o =
      ∑ j, inputs (.inl (o.1, j)) * inputs (.inr (j, o.2)) := by
  have h := (MatrixAlgorithm.correct_iff_entries p).mp hp
    (fun i j => inputs (.inl (i, j))) (fun j k => inputs (.inr (j, k))) o.1 o.2
  have hi : matrixInputs (fun i j => inputs (.inl (i, j)))
      (fun j k => inputs (.inr (j, k))) = inputs := by
    funext x
    cases x <;> rfl
  rw [hi] at h
  exact h

end Family

section BlockIdentities

variable {n₁ n₂ n₃ r m₁ m₂ m₃ : ℕ}

theorem rank_bilinear_identity
    (a : Fin r → Fin n₁ × Fin n₂ → F)
    (b : Fin r → Fin n₂ × Fin n₃ → F)
    (c : Fin r → Fin n₃ × Fin n₁ → F)
    (h : Tensor.matrixCoefficients (K := F) (Fin n₁) (Fin n₂) (Fin n₃) =
      fun x y z => ∑ q, Tensor.rankOne (a q) (b q) (c q) x y z)
    (left : Fin n₁ × Fin n₂ → F) (right : Fin n₂ × Fin n₃ → F)
    (i : Fin n₁) (k : Fin n₃) :
    (∑ q, c q (k, i) * (∑ x, a q x * left x) * (∑ y, b q y * right y)) =
      ∑ j, left (i, j) * right (j, k) := by
  rw [← Tensor.contract_matrixCoefficients left right i k]
  rw [h]
  simp only [Tensor.contract, Tensor.rankOne, Finset.sum_mul, Finset.mul_sum]
  calc
    (∑ q, ∑ y, ∑ x, c q (k, i) * (a q x * left x) * (b q y * right y)) =
        ∑ q, ∑ x, ∑ y, c q (k, i) * (a q x * left x) * (b q y * right y) := by
      apply Finset.sum_congr rfl
      intro q hq
      exact Finset.sum_comm
    _ = ∑ x, ∑ q, ∑ y, c q (k, i) * (a q x * left x) * (b q y * right y) :=
      Finset.sum_comm
    _ = ∑ x, ∑ y, ∑ q, a q x * b q y * c q (k, i) * left x * right y := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro q hq
      ring

theorem block_identity
    (a : Fin r → Fin n₁ × Fin n₂ → F)
    (b : Fin r → Fin n₂ × Fin n₃ → F)
    (c : Fin r → Fin n₃ × Fin n₁ → F)
    (h : Tensor.matrixCoefficients (K := F) (Fin n₁) (Fin n₂) (Fin n₃) =
      fun x y z => ∑ q, Tensor.rankOne (a q) (b q) (c q) x y z)
    (A : Matrix (Fin (n₁ * m₁)) (Fin (n₂ * m₂)) F)
    (B : Matrix (Fin (n₂ * m₂)) (Fin (n₃ * m₃)) F)
    (i : Fin n₁) (k : Fin n₃) (s : Fin m₁) (u : Fin m₃) :
    (∑ q, c q (k, i) * ((leftBlock a A q) * (rightBlock b B q)) s u) =
      (A * B) (join i s) (join k u) := by
  simp only [Matrix.mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hlocal (t : Fin m₂) := rank_bilinear_identity a b c h
    (fun x => A (join x.1 s) (join x.2 t))
    (fun y => B (join y.1 t) (join y.2 u)) i k
  simp only [leftBlock, rightBlock]
  simp_rw [← mul_assoc, hlocal]
  rw [Finset.sum_comm]
  exact (Fintype.sum_prod_type _).symm.trans
    (finProdFinEquiv.sum_comp (fun j => A (join i s) j * B j (join k u)))

end BlockIdentities

section BlockPrograms

variable {n₁ n₂ n₃ r m₁ m₂ m₃ : ℕ}

theorem inputFamily_eval (a : Fin r → Fin n₁ × Fin n₂ → F)
    (b : Fin r → Fin n₂ × Fin n₃ → F)
    (A : Matrix (Fin (n₁ * m₁)) (Fin (n₂ * m₂)) F)
    (B : Matrix (Fin (n₂ * m₂)) (Fin (n₃ * m₃)) F)
    (q : Fin r) (x : MatrixInput m₁ m₂ m₃) :
    (inputFamily a b).eval (matrixInputs A B) (q, x) =
      matrixInputs (leftBlock a A q) (rightBlock b B q) x := by
  cases x with
  | inl x =>
    simp only [inputFamily, Family.eval_expressions, inputExpressions,
      LinearExpression.eval_linear, matrixInputs, leftBlock]
  | inr x =>
    simp only [inputFamily, Family.eval_expressions, inputExpressions,
      LinearExpression.eval_linear, matrixInputs, rightBlock]

theorem inputFamily_cost (a : Fin r → Fin n₁ × Fin n₂ → F)
    (b : Fin r → Fin n₂ × Fin n₃ → F) :
    (inputFamily (m₁ := m₁) (m₂ := m₂) (m₃ := m₃) a b).cost =
      2 * r * (n₁ * n₂ * m₁ * m₂ + n₂ * n₃ * m₂ * m₃) := by
  rw [inputFamily, Family.cost_expressions]
  simp only [Fintype.sum_prod_type, Fintype.sum_sum_type,
    inputExpressions, LinearExpression.cost_linear, Fintype.card_prod,
    Fintype.card_fin, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  ring

theorem recursiveProducts_eval (a : Fin r → Fin n₁ × Fin n₂ → F)
    (b : Fin r → Fin n₂ × Fin n₃ → F)
    (p : MatrixAlgorithm F m₁ m₂ m₃) (hp : p.Correct)
    (A : Matrix (Fin (n₁ * m₁)) (Fin (n₂ * m₂)) F)
    (B : Matrix (Fin (n₂ * m₂)) (Fin (n₃ * m₃)) F)
    (q : Fin r) (s : Fin m₁) (u : Fin m₃) :
    (recursiveProducts a b p).eval (matrixInputs A B) (q, (s, u)) =
      ((leftBlock a A q) * (rightBlock b B q)) s u := by
  rw [recursiveProducts, Family.eval_compose, Family.eval_copies,
    Family.eval_ofMatrix _ hp]
  simp only [inputFamily_eval, matrixInputs, Matrix.mul_apply]

theorem recursiveProducts_cost (a : Fin r → Fin n₁ × Fin n₂ → F)
    (b : Fin r → Fin n₂ × Fin n₃ → F) (p : MatrixAlgorithm F m₁ m₂ m₃) :
    (recursiveProducts a b p).cost =
      2 * r * (n₁ * n₂ * m₁ * m₂ + n₂ * n₃ * m₂ * m₃) + r * p.cost := by
  rw [recursiveProducts, Family.cost_compose, inputFamily_cost,
    Family.cost_copies, Family.cost_ofMatrix]

theorem outputFamily_eval (c : Fin r → Fin n₃ × Fin n₁ → F)
    (inputs : Fin r × (Fin m₁ × Fin m₃) → F)
    (i : Fin n₁) (k : Fin n₃) (s : Fin m₁) (u : Fin m₃) :
    (outputFamily c).eval inputs (join i s, join k u) =
      ∑ q, c q (k, i) * inputs (q, (s, u)) := by
  simp only [outputFamily, Family.eval_expressions, outputExpressions,
    LinearExpression.eval_linear, join, Equiv.symm_apply_apply]

theorem outputFamily_cost (c : Fin r → Fin n₃ × Fin n₁ → F) :
    (outputFamily (m₁ := m₁) (m₃ := m₃) c).cost = 2 * r * n₁ * n₃ * m₁ * m₃ := by
  simp only [outputFamily, Family.cost_expressions, outputExpressions,
    LinearExpression.cost_linear, Fintype.card_fin, Finset.sum_const,
    Finset.card_univ, Fintype.card_prod, smul_eq_mul]
  ring

theorem algorithm_correct
    (a : Fin r → Fin n₁ × Fin n₂ → F)
    (b : Fin r → Fin n₂ × Fin n₃ → F) (c : Fin r → Fin n₃ × Fin n₁ → F)
    (h : Tensor.matrixCoefficients (K := F) (Fin n₁) (Fin n₂) (Fin n₃) =
      fun x y z => ∑ q, Tensor.rankOne (a q) (b q) (c q) x y z)
    (p : MatrixAlgorithm F m₁ m₂ m₃) (hp : p.Correct) : (algorithm a b c p).Correct := by
  intro A B
  funext i k
  obtain ⟨⟨i, s⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨k, u⟩, rfl⟩ := finProdFinEquiv.surjective k
  change ((recursiveProducts a b p).compose (outputFamily c)).eval
    (matrixInputs A B) (join i s, join k u) = _
  rw [Family.eval_compose, outputFamily_eval]
  simp_rw [recursiveProducts_eval a b p hp A B]
  exact block_identity a b c h A B i k s u

theorem algorithm_cost (a : Fin r → Fin n₁ × Fin n₂ → F)
    (b : Fin r → Fin n₂ × Fin n₃ → F) (c : Fin r → Fin n₃ × Fin n₁ → F)
    (p : MatrixAlgorithm F m₁ m₂ m₃) :
    (algorithm a b c p).cost = r * p.cost +
      2 * r * (n₁ * n₂ * m₁ * m₂ + n₂ * n₃ * m₂ * m₃ + n₁ * n₃ * m₁ * m₃) := by
  change ((recursiveProducts a b p).compose (outputFamily c)).cost = _
  rw [Family.cost_compose, recursiveProducts_cost, outputFamily_cost]
  ring

theorem rank_block_step
    (h : Tensor.RankAtMost (Tensor.matrixCoefficients (K := F) (Fin n₁) (Fin n₂) (Fin n₃)) r)
    (p : MatrixAlgorithm F m₁ m₂ m₃) (hp : p.Correct) :
    ∃ q : MatrixAlgorithm F (n₁ * m₁) (n₂ * m₂) (n₃ * m₃), q.Correct ∧
      q.cost = r * p.cost +
        2 * r * (n₁ * n₂ * m₁ * m₂ + n₂ * n₃ * m₂ * m₃ + n₁ * n₃ * m₁ * m₃) := by
  rcases h with ⟨a, b, c, h⟩
  exact ⟨algorithm a b c p, algorithm_correct a b c h p hp, algorithm_cost a b c p⟩

end BlockPrograms

end MatrixMultiplication.Arithmetic.RecursiveBlock

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Entropy_ComplexFiniteEntropy
attribute [-simp] _root_.OAI.MatrixMultiplication.CompletionProductLaws.independentProduct_mass _root_.OAI.MatrixMultiplication.CompletionProductLaws.sigmaJoint_mass _root_.OAI.MatrixMultiplication.ConditionalLabels.normalizedCountLaw_mass _root_.OAI.MatrixMultiplication.Foundation.FiniteLabelHierarchy.prefixLaw_succ _root_.OAI.MatrixMultiplication.Foundation.FiniteLabelHierarchy.prefixLaw_succ_mass _root_.OAI.MatrixMultiplication.Foundation.FiniteLabelHierarchy.prefixLaw_zero_mass _root_.OAI.MatrixMultiplication.Foundation.FiniteLaw.uniform_mass _root_.OAI.MatrixMultiplication.Foundation.RationalLaw.toFiniteLaw_mass _root_.OAI.MatrixMultiplication.Foundation.entropyTerm_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

namespace MatrixMultiplication.Foundation

open scoped BigOperators

namespace FiniteLaw

variable {A B : Type*} [Fintype A] [Fintype B]

theorem map_entropy_of_injective (p : FiniteLaw A) (f : A → B)
    (hf : Function.Injective f) : finiteEntropy (p.map f).mass = finiteEntropy p.mass := by
  classical
  have hterm (b : B) : entropyTerm ((p.map f).mass b) =
      ∑ a, if f a = b then entropyTerm (p.mass a) else 0 := by
    by_cases hb : ∃ a, f a = b
    · obtain ⟨a, rfl⟩ := hb
      rw [map_mass_apply p f hf]
      simp [hf.eq_iff]
    · simp [map_mass, not_exists.mp hb]
  unfold finiteEntropy
  simp_rw [hterm]
  rw [Finset.sum_comm]
  simp

end FiniteLaw
end MatrixMultiplication.Foundation

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Entropy_ComplexEntropyContinuity
attribute [-simp] _root_.OAI.MatrixMultiplication.CompletionProductLaws.independentProduct_mass _root_.OAI.MatrixMultiplication.CompletionProductLaws.sigmaJoint_mass _root_.OAI.MatrixMultiplication.ConditionalLabels.normalizedCountLaw_mass _root_.OAI.MatrixMultiplication.Foundation.FiniteLabelHierarchy.prefixLaw_succ _root_.OAI.MatrixMultiplication.Foundation.FiniteLabelHierarchy.prefixLaw_succ_mass _root_.OAI.MatrixMultiplication.Foundation.FiniteLabelHierarchy.prefixLaw_zero_mass _root_.OAI.MatrixMultiplication.Foundation.RationalLaw.toFiniteLaw_mass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

open scoped Topology
open Filter

namespace MatrixMultiplication.Foundation

theorem mul_entropyTerm_inv (x : ℝ) : x * entropyTerm x⁻¹ = Real.log x := by
  by_cases hx : x = 0
  · simp [hx]
  · simp only [entropyTerm, Real.log_inv]
    calc
      _ = (x * x⁻¹) * Real.log x := by ring
      _ = Real.log x := by rw [mul_inv_cancel₀ hx, one_mul]

theorem finiteEntropy_uniform {A : Type*} [Fintype A] :
    finiteEntropy (fun _a : A => (Fintype.card A : ℝ)⁻¹) =
      Real.log (Fintype.card A) := by
  simp only [finiteEntropy, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_entropyTerm_inv (Fintype.card A)

theorem finiteEntropy_deterministic {A : Type*} [Fintype A] [DecidableEq A]
    (a : A) : finiteEntropy (fun b => if b = a then 1 else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro b hb
  change entropyTerm (if b = a then 1 else 0) = 0
  split_ifs <;> simp

theorem tendsto_finiteEntropy_of_tendsto {I A : Type*} [Fintype A]
    {l : Filter I} {p : I → A → ℝ} {q : A → ℝ}
    (h : ∀ a, Tendsto (fun i => p i a) l (𝓝 (q a))) :
    Tendsto (fun i => finiteEntropy (p i)) l (𝓝 (finiteEntropy q)) :=
  continuous_finiteEntropy.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr h)

namespace FiniteLaw

variable {A : Type*} [Fintype A]

@[simp] theorem uniform_entropy [Nonempty A] :
    finiteEntropy (uniform A).mass = Real.log (Fintype.card A) :=
  finiteEntropy_uniform

@[simp] theorem pure_entropy (a : A) : finiteEntropy (pure a).mass = 0 := by
  classical
  exact finiteEntropy_deterministic a

theorem entropy_tendsto {I : Type*} {l : Filter I}
    {p : I → FiniteLaw A} {q : FiniteLaw A}
    (h : ∀ a, Tendsto (fun i => (p i).mass a) l (𝓝 (q.mass a))) :
    Tendsto (fun i => finiteEntropy (p i).mass) l (𝓝 (finiteEntropy q.mass)) :=
  tendsto_finiteEntropy_of_tendsto h

end FiniteLaw
end MatrixMultiplication.Foundation

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Completion_Laws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.CompletionLaws

open MatrixMultiplication.Foundation
open scoped BigOperators

variable {A B X : Type*} [Fintype A] [Fintype B] [Fintype X]

theorem independent_entropy (p : FiniteLaw A) (q : FiniteLaw B) :
    finiteEntropy (p.joint (fun _ => q)).mass =
      finiteEntropy p.mass + finiteEntropy q.mass := by
  rw [FiniteLaw.joint_entropy, ← Finset.sum_mul, p.total, one_mul]

end MatrixMultiplication.CompletionLaws

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Completion_Conditioning
attribute [-simp] _root_.OAI.MatrixMultiplication.CompletionProductLaws.independentProduct_mass _root_.OAI.MatrixMultiplication.CompletionProductLaws.sigmaJoint_mass _root_.OAI.MatrixMultiplication.ConditionalLabels.normalizedCountLaw_mass _root_.OAI.MatrixMultiplication.Foundation.FiniteLabelHierarchy.prefixLaw_succ _root_.OAI.MatrixMultiplication.Foundation.FiniteLabelHierarchy.prefixLaw_succ_mass _root_.OAI.MatrixMultiplication.Foundation.FiniteLabelHierarchy.prefixLaw_zero_mass _root_.OAI.MatrixMultiplication.Foundation.RationalLaw.toFiniteLaw_mass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.CompletionLaws

open MatrixMultiplication.Foundation
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {A X : Type*} [Fintype A] [Fintype X]

theorem condition_mass (p : FiniteLaw A) (P : A → Prop)
    (h : 0 < eventMass p P) (a : {a // P a}) :
    (condition p P h).mass a = p.mass a.val / eventMass p P := rfl

theorem condition_coordinate_mass (p : FiniteLaw A) (f : A → X) (Q : X → Prop)
    (h : 0 < eventMass p (fun a => Q (f a))) (x : X) :
    ((condition p (fun a => Q (f a)) h).map (fun a => f a.val)).mass x =
      if Q x then (p.map f).mass x / eventMass p (fun a => Q (f a)) else 0 := by
  rw [FiniteLaw.map_mass]
  simp only [condition_mass]
  have hsum :
      (∑ a : {a // Q (f a)}, if f a.val = x then
        p.mass a.val / eventMass p (fun a => Q (f a)) else 0) =
      ∑ a, if Q (f a) then
        (if f a = x then p.mass a / eventMass p (fun a => Q (f a)) else 0) else 0 :=
    sum_subtype_indicator (fun a => Q (f a))
      (fun a => if f a = x then p.mass a / eventMass p (fun a => Q (f a)) else 0)
  rw [hsum]
  by_cases hx : Q x
  · rw [ite_eq_left hx, FiniteLaw.map_mass, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : f a = x
    · simp [ha, hx]
    · simp [ha]
  · rw [ite_eq_right hx]
    apply Finset.sum_eq_zero
    intro a _
    by_cases ha : f a = x
    · simp [ha, hx]
    · simp [ha]

theorem eventMass_coordinate (p : FiniteLaw A) (f : A → X) (Q : X → Prop) :
    eventMass p (fun a => Q (f a)) = eventMass (p.map f) Q := by
  rw [eventMass, eventMass, sum_subtype_indicator, sum_subtype_indicator]
  simp only [FiniteLaw.map_mass]
  calc
    (∑ a, if Q (f a) then p.mass a else 0) =
        ∑ a, ∑ x, if Q x then (if f a = x then p.mass a else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_eq_single (f a)]
      · simp
      · intro x _ hne
        simp [Ne.symm hne]
      · simp
    _ = ∑ x, ∑ a, if Q x then (if f a = x then p.mass a else 0) else 0 :=
      Finset.sum_comm
    _ = ∑ x, if Q x then ∑ a, if f a = x then p.mass a else 0 else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp

theorem transport_mass {B : Type*} [Fintype B] (e : A ≃ B) (p : FiniteLaw A) (a : A) :
    (transport e p).mass (e a) = p.mass a := p.map_mass_apply e e.injective a

theorem transport_entropy {B : Type*} [Fintype B] (e : A ≃ B) (p : FiniteLaw A) :
    finiteEntropy (transport e p).mass = finiteEntropy p.mass :=
  p.map_entropy_of_injective e e.injective

end MatrixMultiplication.CompletionLaws

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Tensor_ComplexTensorSymmetrization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {K X Y Z U V W : Type*} [CommSemiring K]

theorem RankAtMost.directSum_pullback {ι X' Y' Z' : Type*} [DecidableEq ι]
    {T : ι → Tensor K X Y Z} {r : ℕ} (h : RankAtMost (directSum T) r)
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    RankAtMost (directSum (fun i => Tensor.pullback fx fy fz (T i))) r :=
  h.pullback (fun x : ι × X' => (x.1, fx x.2))
    (fun y : ι × Y' => (y.1, fy y.2)) (fun z : ι × Z' => (z.1, fz z.2))

theorem directSum_power {ι : Type*} [DecidableEq ι]
    (T : ι → Tensor K X Y Z) (n : ℕ) :
    pullback (directSumPowerEquiv ι X n) (directSumPowerEquiv ι Y n)
      (directSumPowerEquiv ι Z n) (power (directSum T) n) =
      directSum (fun f : Fin n → ι =>
        fun x y z => ∏ i, T (f i) (x i) (y i) (z i)) := by
  funext x y z
  change (∏ i, if x.1 i = y.1 i ∧ x.1 i = z.1 i then
      T (x.1 i) (x.2 i) (y.2 i) (z.2 i) else 0) =
    if x.1 = y.1 ∧ x.1 = z.1 then
      ∏ i, T (x.1 i) (x.2 i) (y.2 i) (z.2 i) else 0
  simp only [Fintype.prod_ite_zero, forall_and, ← funext_iff]

theorem directSum_const_power {ι : Type*} [DecidableEq ι]
    (T : Tensor K X Y Z) (n : ℕ) :
    pullback (directSumPowerEquiv ι X n) (directSumPowerEquiv ι Y n)
      (directSumPowerEquiv ι Z n) (power (directSum (fun _ : ι => T)) n) =
      directSum (fun _ : Fin n → ι => power T n) :=
  directSum_power (fun _ : ι => T) n

theorem RankAtMost.directSum_const_of_power {ι : Type*} [DecidableEq ι]
    {T : Tensor K X Y Z} {n R : ℕ}
    (h : RankAtMost (Tensor.power (directSum (fun _ : ι => T)) n) R) :
    RankAtMost (directSum (fun _ : Fin n → ι => Tensor.power T n)) R := by
  have h' := h.pullback (directSumPowerEquiv ι X n)
    (directSumPowerEquiv ι Y n) (directSumPowerEquiv ι Z n)
  rw [Tensor.directSum_const_power] at h'
  exact h'

section Rectangular

variable {A B C : Type*}

variable [DecidableEq A] [DecidableEq B] [DecidableEq C]

theorem matrixCoefficients_directSum_rank_of_power
    {ι : Type*} [DecidableEq ι] {n R : ℕ}
    (h : RankAtMost
      (power (directSum (fun _ : ι => matrixCoefficients (K := K) A B C)) n) R) :
    RankAtMost (directSum (fun _ : Fin n → ι =>
      matrixCoefficients (K := K) (Fin n → A) (Fin n → B) (Fin n → C))) R := by
  have h' := h.directSum_const_of_power.directSum_pullback
    (fun x : (Fin n → A) × (Fin n → B) => fun i => (x.1 i, x.2 i))
    (fun y : (Fin n → B) × (Fin n → C) => fun i => (y.1 i, y.2 i))
    (fun z : (Fin n → C) × (Fin n → A) => fun i => (z.1 i, z.2 i))
  have heq : pullback
      (fun x : (Fin n → A) × (Fin n → B) => fun i => (x.1 i, x.2 i))
      (fun y : (Fin n → B) × (Fin n → C) => fun i => (y.1 i, y.2 i))
      (fun z : (Fin n → C) × (Fin n → A) => fun i => (z.1 i, z.2 i))
      (power (matrixCoefficients (K := K) A B C) n) =
      matrixCoefficients (Fin n → A) (Fin n → B) (Fin n → C) := by
    funext x y z
    exact matrixCoefficients_power n x y z
  simpa only [heq] using h'

end Rectangular

end Tensor
end MatrixMultiplication.Foundation

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Entropy_ComplexHierarchyEntropy
attribute [-instance] _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.labelRecordZero_subsingleton
attribute [-simp] _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_auxiliaryRank _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_columns _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_inner _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_multiplicity _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_occurrences _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_rows _root_.OAI.MatrixMultiplication.CompletionProductLaws.independentProduct_mass _root_.OAI.MatrixMultiplication.CompletionProductLaws.sigmaJoint_mass _root_.OAI.MatrixMultiplication.ConditionalLabels.normalizedCountLaw_mass _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_inner _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_multiplicity _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_outer _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_rank _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.appendCode_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.appendPrefix_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.decodedFine_eq_geometryDecode _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.encodeSourceWord_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.finePrefix_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.mem_conditionalFinset _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.oldPrefix_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.rootPrefixWord_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourcePrefixEquiv_apply_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourcePrefixEquiv_symm_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourceSymbol_encodeSourceWord _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourceSymbol_record _root_.OAI.MatrixMultiplication.Foundation.FiniteLaw.pure_entropy _root_.OAI.MatrixMultiplication.Foundation.FiniteLaw.uniform_entropy _root_.OAI.MatrixMultiplication.Foundation.FiniteLaw.uniform_mass _root_.OAI.MatrixMultiplication.Foundation.RationalLaw.toFiniteLaw_mass _root_.OAI.MatrixMultiplication.Foundation.entropyTerm_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

namespace MatrixMultiplication.Foundation

open scoped BigOperators

universe u v

noncomputable section

namespace FiniteLabelHierarchy

variable {Label : ℕ → Type u} [∀ n, Fintype (Label n)] {depth : ℕ}

theorem prefixLaw_entropy (h : FiniteLabelHierarchy Label depth)
    (n : ℕ) (hn : n ≤ depth) :
    finiteEntropy (h.prefixLaw n hn).mass =
      ∑ j ∈ Finset.range n, h.refinementEntropy j := by
  induction n with
  | zero =>
      simp [prefixLaw, finiteEntropy, entropyTerm, LabelRecord]
  | succ n ih =>
      rw [prefixLaw_entropy_succ h n hn,
        ih (Nat.le_of_succ_le hn), Finset.sum_range_succ]

theorem recordLaw_entropy (h : FiniteLabelHierarchy Label depth) :
    finiteEntropy h.recordLaw.mass =
      ∑ j ∈ Finset.range depth, h.refinementEntropy j :=
  h.prefixLaw_entropy depth le_rfl

theorem refinementEntropy_sum_of_injective_record
    {A : Type v} [Fintype A] (h : FiniteLabelHierarchy Label depth)
    (p : FiniteLaw A) (record : A → LabelRecord Label depth)
    (hinjective : Function.Injective record)
    (hmass : h.recordLaw.mass = (p.map record).mass) :
    (∑ j ∈ Finset.range depth, h.refinementEntropy j) = finiteEntropy p.mass := by
  calc
    (∑ j ∈ Finset.range depth, h.refinementEntropy j) =
        finiteEntropy h.recordLaw.mass := h.recordLaw_entropy.symm
    _ = finiteEntropy (p.map record).mass := congrArg finiteEntropy hmass
    _ = finiteEntropy p.mass := p.map_entropy_of_injective record hinjective

theorem ofLawLabels_refinementEntropy_sum {A : Type v} [Fintype A]
    (p : FiniteLaw A) (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    (∑ j ∈ Finset.range depth,
      (ofLawLabels p labels depth).refinementEntropy j) = finiteEntropy p.mass := by
  apply (ofLawLabels p labels depth).refinementEntropy_sum_of_injective_record
    p (labelRecordOf labels depth) hinjective
  exact ofLawLabels_prefixLaw_mass p labels depth depth le_rfl

end FiniteLabelHierarchy

end
end MatrixMultiplication.Foundation

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Separation_ComplexFiniteControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

namespace MatrixMultiplication.Foundation
namespace FiniteControl

open scoped BigOperators

theorem exists_common_bank_multiple {Node : Type*} [Fintype Node]
    (denominator blockSize : Node → ℕ)
    (denominator_pos : ∀ node, 0 < denominator node)
    (blockSize_pos : ∀ node, 0 < blockSize node) :
    ∃ bank : ℕ, 0 < bank ∧
      ∀ node, denominator node * blockSize node ∣ bank := by
  classical
  refine ⟨∏ node, denominator node * blockSize node, ?_, ?_⟩
  · exact Finset.prod_pos fun node _ =>
      Nat.mul_pos (denominator_pos node) (blockSize_pos node)
  · intro node
    exact Finset.dvd_prod_of_mem (fun node => denominator node * blockSize node)
      (Finset.mem_univ node)

theorem exists_exact_rational_tiling {Node : Type*} [Fintype Node]
    (weight : Node → ℚ) (nonnegative : ∀ node, 0 ≤ weight node)
    (blockSize : Node → ℕ) (blockSize_pos : ∀ node, 0 < blockSize node) :
    ∃ bank : ℕ, 0 < bank ∧ ∀ node, ∃ copies : ℕ,
      (bank : ℚ) * weight node = (copies * blockSize node : ℕ) := by
  obtain ⟨bank, bank_pos, divisible⟩ := exists_common_bank_multiple
    (fun node => (weight node).den) blockSize
    (fun node => (weight node).den_pos) blockSize_pos
  refine ⟨bank, bank_pos, ?_⟩
  intro node
  obtain ⟨multiple, hmultiple⟩ := divisible node
  refine ⟨multiple * (weight node).num.toNat, ?_⟩
  have hnum : ((weight node).num.toNat : ℚ) = ((weight node).num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr (nonnegative node))
  have hden : ((weight node).den : ℚ) ≠ 0 := by
    exact_mod_cast (weight node).den_ne_zero
  calc
    (bank : ℚ) * weight node =
        (bank : ℚ) * (((weight node).num : ℚ) / ((weight node).den : ℚ)) := by
      rw [(weight node).num_div_den]
    _ = ((multiple * (weight node).num.toNat) * blockSize node : ℕ) := by
      rw [hmultiple]
      push_cast
      rw [hnum]
      field_simp [hden]

end FiniteControl
end MatrixMultiplication.Foundation

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Separation_ComplexRationalTypes
attribute [-simp] _root_.OAI.MatrixMultiplication.CompletionProductLaws.independentProduct_mass _root_.OAI.MatrixMultiplication.CompletionProductLaws.sigmaJoint_mass _root_.OAI.MatrixMultiplication.ConditionalLabels.normalizedCountLaw_mass _root_.OAI.MatrixMultiplication.Foundation.FiniteLabelHierarchy.prefixLaw_succ _root_.OAI.MatrixMultiplication.Foundation.FiniteLabelHierarchy.prefixLaw_succ_mass _root_.OAI.MatrixMultiplication.Foundation.FiniteLabelHierarchy.prefixLaw_zero_mass _root_.OAI.MatrixMultiplication.Foundation.FiniteLaw.pure_entropy _root_.OAI.MatrixMultiplication.Foundation.FiniteLaw.uniform_entropy _root_.OAI.MatrixMultiplication.Foundation.FiniteLaw.uniform_mass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

namespace MatrixMultiplication.Foundation

open scoped BigOperators

namespace RationalLaw

variable {A B : Type*} [Fintype A] [Fintype B]

theorem exists_exact_counts (p : RationalLaw A) :
    ∃ D : ℕ, 0 < D ∧ ∃ counts : A → ℕ,
      (∑ a, counts a) = D ∧
      ∀ a, (counts a : ℚ) = (D : ℚ) * p.mass a := by
  classical
  obtain ⟨D, hD, hcopies⟩ := FiniteControl.exists_exact_rational_tiling
    p.mass p.nonneg (fun _ => 1) (fun _ => Nat.zero_lt_one)
  choose counts hcounts using hcopies
  have hc : ∀ a, (counts a : ℚ) = (D : ℚ) * p.mass a := by
    intro a
    simpa using (hcounts a).symm
  refine ⟨D, hD, counts, ?_, hc⟩
  have hsum : (∑ a, (counts a : ℚ)) = (D : ℚ) := by
    simp_rw [hc]
    rw [← Finset.mul_sum, p.total, mul_one]
  exact_mod_cast hsum

theorem exact_counts_real_mass (p : RationalLaw A) {D : ℕ} (hD : 0 < D)
    {counts : A → ℕ}
    (hcounts : ∀ a, (counts a : ℚ) = (D : ℚ) * p.mass a) (a : A) :
    (counts a : ℝ) / (D : ℝ) = p.toFiniteLaw.mass a := by
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  apply (div_eq_iff hDr).2
  have hc : (counts a : ℝ) = (D : ℝ) * (p.mass a : ℝ) := by
    exact_mod_cast hcounts a
  simpa only [toFiniteLaw_mass, mul_comm] using hc

theorem exists_type_representation (p : RationalLaw A) :
    ∃ counts : A → ℕ, 0 < ∑ a, counts a ∧
      ∀ a, (counts a : ℝ) / (∑ a, counts a : ℕ) = p.toFiniteLaw.mass a := by
  obtain ⟨D, hD, counts, hsum, hcounts⟩ := p.exists_exact_counts
  refine ⟨counts, by simpa only [hsum] using hD, ?_⟩
  intro a
  rw [hsum]
  exact p.exact_counts_real_mass hD hcounts a

end RationalLaw

private theorem exists_nonnegative_rat_below (x : ℝ) (hx : 0 ≤ x)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ r : ℚ, 0 ≤ r ∧ (r : ℝ) ≤ x ∧ (r = 0 ↔ x = 0) ∧
      |(r : ℝ) - x| < δ := by
  by_cases hx0 : x = 0
  · subst x
    exact ⟨0, le_rfl, by simp, by simp, by simpa using hδ⟩
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hlo : max 0 (x - δ) < x := max_lt hxpos (by linarith)
  obtain ⟨r, hrlo, hrhi⟩ := exists_rat_btwn hlo
  have hrpos : (0 : ℝ) < r := lt_of_le_of_lt (le_max_left _ _) hrlo
  have hrposq : (0 : ℚ) < r := by exact_mod_cast hrpos
  refine ⟨r, hrposq.le, hrhi.le,
    iff_of_false (ne_of_gt hrposq) hx0, ?_⟩
  have hrlo' : x - δ < r := lt_of_le_of_lt (le_max_right _ _) hrlo
  rw [abs_of_nonpos (sub_nonpos.mpr hrhi.le)]
  linarith

namespace FiniteLaw

variable {A : Type*} [Fintype A]

theorem exists_rational_approximation (p : FiniteLaw A) (ε : ℝ) (hε : 0 < ε) :
    ∃ q : RationalLaw A,
      (∀ a, q.mass a = 0 ↔ p.mass a = 0) ∧
      ∀ a, |(q.mass a : ℝ) - p.mass a| < ε := by
  classical
  have hpivot : ∃ a, 0 < p.mass a := by
    by_contra h
    have hnonpos : ∀ a, p.mass a ≤ 0 :=
      fun a => le_of_not_gt (fun ha => h ⟨a, ha⟩)
    have hsum : (∑ a, p.mass a) ≤ 0 :=
      Finset.sum_nonpos (fun a _ => hnonpos a)
    rw [p.total] at hsum
    norm_num at hsum
  obtain ⟨a₀, ha₀⟩ := hpivot
  let δ : ℝ := ε / ((Fintype.card A : ℝ) + 1)
  have hcard : 0 ≤ (Fintype.card A : ℝ) := Nat.cast_nonneg _
  have hden : 0 < (Fintype.card A : ℝ) + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hden
  have hδε : δ * ((Fintype.card A : ℝ) + 1) = ε :=
    div_mul_cancel₀ ε (ne_of_gt hden)
  have hcardδ : 0 ≤ (Fintype.card A : ℝ) * δ := mul_nonneg hcard hδ.le
  have hδle : δ ≤ ε := by nlinarith
  choose r hrnonneg hrle hrzero hrclose using
    fun a => exists_nonnegative_rat_below (p.mass a) (p.nonneg a) δ hδ
  have hsum : (∑ a, (r a : ℝ)) ≤ 1 := by
    calc
      (∑ a, (r a : ℝ)) ≤ ∑ a, p.mass a :=
        Finset.sum_le_sum (fun a _ => hrle a)
      _ = 1 := p.total
  have hrest : 0 ≤ 1 - ∑ a, (r a : ℝ) := sub_nonneg.mpr hsum
  have hrestq : (0 : ℚ) ≤ 1 - ∑ a, r a := by exact_mod_cast hrest
  have hrest_le : 1 - ∑ a, (r a : ℝ) ≤ (Fintype.card A : ℝ) * δ := by
    calc
      1 - ∑ a, (r a : ℝ) = ∑ a, (p.mass a - (r a : ℝ)) := by
        rw [Finset.sum_sub_distrib, p.total]
      _ ≤ ∑ _a : A, δ := by
        apply Finset.sum_le_sum
        intro a _
        have h := (abs_lt.mp (hrclose a)).1
        linarith
      _ = (Fintype.card A : ℝ) * δ := by simp
  let q : RationalLaw A :=
    { mass := fun a => r a + if a = a₀ then 1 - ∑ b, r b else 0
      nonneg := by
        intro a
        apply add_nonneg (hrnonneg a)
        split_ifs
        · exact hrestq
        · exact le_rfl
      total := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
        ring }
  refine ⟨q, ?_, ?_⟩
  · intro a
    by_cases ha : a = a₀
    · subst a
      have hrpos : 0 < r a₀ :=
        lt_of_le_of_ne (hrnonneg a₀) (Ne.symm (fun hz => (ne_of_gt ha₀) ((hrzero a₀).mp hz)))
      have hqpos : 0 < q.mass a₀ := by
        dsimp [q]
        simp only [ite_true, if_true]
        linarith
      exact iff_of_false (ne_of_gt hqpos) (ne_of_gt ha₀)
    · simpa only [q, ite_eq_right ha, add_zero] using hrzero a
  · intro a
    by_cases ha : a = a₀
    · have hqcast : (q.mass a : ℝ) =
          (r a : ℝ) + (1 - ∑ b, (r b : ℝ)) := by
        simp [q, ha]
      rw [hqcast]
      have habs : |(r a : ℝ) + (1 - ∑ b, (r b : ℝ)) - p.mass a| ≤
          |(r a : ℝ) - p.mass a| + (1 - ∑ b, (r b : ℝ)) := by
        calc
          _ = |((r a : ℝ) - p.mass a) + (1 - ∑ b, (r b : ℝ))| := by
            congr 1
            ring
          _ ≤ |(r a : ℝ) - p.mass a| + |1 - ∑ b, (r b : ℝ)| := abs_add_le _ _
          _ = _ := by rw [abs_of_nonneg hrest]
      have hclose := hrclose a
      nlinarith
    · simpa only [q, ite_eq_right ha, add_zero] using
        lt_of_lt_of_le (hrclose a) hδle

end FiniteLaw

end MatrixMultiplication.Foundation

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Entropy_ConditionalLabels
attribute [-instance] _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.labelRecordZero_subsingleton
attribute [-simp] _root_.OAI.MatrixMultiplication.CW75ReorderedExecution.pairingProduct_zero _root_.OAI.MatrixMultiplication.CompletionExecution.pairingProduct_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

namespace MatrixMultiplication

open MatrixMultiplication.Foundation Filter
open scoped Topology BigOperators Classical

namespace ConditionalLabels

universe u v

section PairAccounting

variable {I : Type u} [Fintype I]

theorem pairingRate_sum (rate : I → ℝ) (reader : I → ReaderPair) :
    pairingRate rate reader .xy + pairingRate rate reader .xz +
      pairingRate rate reader .yz = ∑ i, rate i := by
  simp only [pairingRate, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases reader i <;> simp

end PairAccounting

section SourceHierarchy

variable {A : Type u} [Fintype A] {Label : ℕ → Type v}
  [∀ n, Fintype (Label n)]

open StageHierarchyResources HierarchySeparationRates

theorem lawPairingRate_sum (p : FiniteLaw A) (labels : ∀ n, A → Label n)
    (depth : ℕ) (reader : Fin depth → ReaderPair)
    (complete : Function.Injective (labelRecordOf labels depth)) :
    lawPairingRate p labels depth reader .xy +
      lawPairingRate p labels depth reader .xz +
      lawPairingRate p labels depth reader .yz = finiteEntropy p.mass := by
  rw [lawPairingRate, lawPairingRate, lawPairingRate, pairingRate_sum,
    Fin.sum_univ_eq_sum_range]
  exact FiniteLabelHierarchy.ofLawLabels_refinementEntropy_sum p labels depth complete

end SourceHierarchy
end ConditionalLabels
end MatrixMultiplication

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Completion_Labels
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.labelRecordZero_subsingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

universe uCoord

namespace MatrixMultiplication.CompletionLabels.TopologicalFlatten

open MatrixMultiplication.Foundation RecursiveCompletion

universe u v

theorem labelRecordOf_eq_prefix {A : Type u} {Label : ℕ → Type v}
    (labels : ∀ n, A → Label n) {a b : A} :
    ∀ {m k : ℕ}, k ≤ m →
      labelRecordOf labels m a = labelRecordOf labels m b →
      labelRecordOf labels k a = labelRecordOf labels k b := by
  intro m
  induction m with
  | zero =>
      intro k hk _
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      rfl
  | succ m ih =>
      intro k hk h
      rcases Nat.eq_or_lt_of_le hk with hk | hk
      · subst k
        exact h
      · exact ih (Nat.le_of_lt_succ hk) (congrArg Prod.fst h)

theorem label_eq_of_record_eq {A : Type u} {Label : ℕ → Type v}
    (labels : ∀ n, A → Label n) {depth n : ℕ} {a b : A}
    (h : labelRecordOf labels depth a = labelRecordOf labels depth b)
    (hn : n < depth) : labels n a = labels n b := by
  have hp : labelRecordOf labels (n + 1) a =
      labelRecordOf labels (n + 1) b :=
    labelRecordOf_eq_prefix labels (Nat.succ_le_of_lt hn) h
  exact congrArg Prod.snd hp

end MatrixMultiplication.CompletionLabels.TopologicalFlatten

namespace MatrixMultiplication.CompletionLabels.TopologicalFlatten.Program

open MatrixMultiplication.Foundation RecursiveCompletion

universe u v w z

variable {A : Type u} {Coord : Color → Type v}
  {Context : Type z} {Code : Type w} {depth : ℕ}

theorem pow_labels [Inhabited Code] (p : Program A Coord Context Code depth) (m : ℕ)
    (a : Fin m → A) (i : Fin m) (n : ℕ) (hn : n < depth) :
    (p.pow m).labels (i.val * depth + n) a = p.labels n (a i) :=
  powLabel_at p m a i hn

end MatrixMultiplication.CompletionLabels.TopologicalFlatten.Program

namespace MatrixMultiplication.CompletionLabels

open MatrixMultiplication.Foundation RecursiveCompletion TopologicalFlatten

universe w

end MatrixMultiplication.CompletionLabels
namespace MatrixMultiplication.CompletionLabels

open MatrixMultiplication.Foundation RecursiveCompletion TopologicalFlatten

attribute [local instance] Classical.propDecidable Classical.decEq

universe u

variable {X Y Z : Type uCoord} {Code : Type u} {depth : ℕ}

theorem terminationInherited_complete (S : FlaggedTensor X Y Z) (first second : Color)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side)
    (complete : p.Complete) :
    (terminationInherited S first second p view_eq).Complete := by
  unfold terminationInherited
  exact p.pullback_complete
    (fun a : RetainedLeaf S first second => a.val)
    (fun side a => coordinate a.val.val side) (fun _ => id)
    (fun side a => (view_eq side a.val).symm) complete Subtype.val_injective

theorem terminationProgram_complete [Inhabited Code]
    (S : FlaggedTensor X Y Z) (first second : Color) (distinct : first ≠ second)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (context_eq : ∀ a, p.context a = leafColor S a)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side)
    (complete : p.Complete) :
    (terminationProgram S first second distinct p context_eq view_eq).Complete := by
  exact Program.append_complete
    ((terminationRoot S first second distinct).recode Sum.inl
      (terminationDecodeColor first) (fun _ => rfl))
    ((terminationInherited S first second p view_eq).recode Sum.inr
      terminationDecodeOld (fun _ => rfl))
    (by intro side a; rfl)
    (fun _ prior => terminationDecodeColor first (prior 0))
    (by
      intro a
      change leafColor S a.val = p.context a.val
      exact (context_eq a.val).symm)
    (Program.recode_complete (terminationInherited S first second p view_eq)
      Sum.inr terminationDecodeOld (fun _ => rfl)
      (terminationInherited_complete S first second p view_eq complete))

theorem terminationRecord_injective [Inhabited Code]
    (S : FlaggedTensor X Y Z) (first second : Color) (distinct : first ≠ second)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (context_eq : ∀ a, p.context a = leafColor S a)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side)
    (complete : p.Complete) :
    Function.Injective (labelRecordOf
      (terminationProgram S first second distinct p context_eq view_eq).labels (1 + depth)) := by
  intro a b h
  apply terminationProgram_complete S first second distinct p context_eq view_eq complete a b rfl
  intro n hn
  exact label_eq_of_record_eq _ h hn

end MatrixMultiplication.CompletionLabels

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Completion_ProductLaws
attribute [-simp] _root_.OAI.MatrixMultiplication.ConditionalLabels.normalizedCountLaw_mass _root_.OAI.MatrixMultiplication.Foundation.FiniteLabelHierarchy.prefixLaw_succ _root_.OAI.MatrixMultiplication.Foundation.FiniteLabelHierarchy.prefixLaw_succ_mass _root_.OAI.MatrixMultiplication.Foundation.FiniteLabelHierarchy.prefixLaw_zero_mass _root_.OAI.MatrixMultiplication.Foundation.RationalLaw.toFiniteLaw_mass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.CompletionProductLaws

open MatrixMultiplication.Foundation
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {I : Type*} [Fintype I] [DecidableEq I] {A : I → Type*} [∀ i, Fintype (A i)]

theorem entropyTerm_prod {J : Type*} [DecidableEq J] (s : Finset J) (f : J → ℝ) :
    entropyTerm (∏ i ∈ s, f i) =
      ∑ i ∈ s, ∏ j ∈ s, if j = i then entropyTerm (f j) else f j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, entropyTerm_mul, Finset.sum_insert ha]
    have hrest : (∏ j ∈ s, if j = a then entropyTerm (f j) else f j) =
        ∏ j ∈ s, f j := by
      apply Finset.prod_congr rfl
      intro j hj
      have hja : j ≠ a := by rintro rfl; exact ha hj
      simp only [hja, ite_false, if_false]
    rw [Finset.prod_insert ha, ite_eq_left rfl, hrest, ih]
    rw [Finset.mul_sum]
    apply congrArg₂ (· + ·)
    · ring
    · apply Finset.sum_congr rfl
      intro i hi
      have hai : a ≠ i := by rintro rfl; exact ha hi
      rw [Finset.prod_insert ha, ite_eq_right hai]

theorem independentProduct_entropy (p : ∀ i, FiniteLaw (A i)) :
    finiteEntropy (independentProduct p).mass =
      ∑ i, finiteEntropy (p i).mass := by
  classical
  simp only [finiteEntropy, independentProduct_mass, entropyTerm_prod]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Fintype.prod_sum (fun j (a : A j) =>
    if j = i then entropyTerm ((p j).mass a) else (p j).mass a)]
  calc
    (∏ j, ∑ a : A j, if j = i then entropyTerm ((p j).mass a) else (p j).mass a) =
        ∏ j, if j = i then (∑ a : A j, entropyTerm ((p j).mass a)) else 1 := by
      apply Finset.prod_congr rfl
      intro j _
      by_cases hji : j = i <;> simp only [hji, ite_true, if_true, ite_false, if_false, (p j).total]
    _ = _ := Fintype.prod_ite_eq' i _

theorem independentProduct_map_mass
    {B : I → Type*} [∀ i, Fintype (B i)]
    (p : ∀ i, FiniteLaw (A i)) (f : ∀ i, A i → B i) (y : ∀ i, B i) :
    ((independentProduct p).map (fun x i => f i (x i))).mass y =
      ∏ i, ((p i).map (f i)).mass (y i) := by
  classical
  rw [FiniteLaw.map_mass]
  calc
    (∑ x, if (fun i => f i (x i)) = y then (independentProduct p).mass x else 0) =
        ∑ x : ∀ i, A i, ∏ i, if f i (x i) = y i then (p i).mass (x i) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : ∀ i, f i (x i) = y i
      · simp [h]
      · have hne : (fun i => f i (x i)) ≠ y := fun he => h (congrFun he)
        rw [ite_eq_right hne]
        obtain ⟨i, hi⟩ := not_forall.mp h
        symm
        exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
    _ = ∏ i, ∑ a, if f i a = y i then (p i).mass a else 0 :=
      (Fintype.prod_sum (fun i (a : A i) => if f i a = y i then (p i).mass a else 0)).symm
    _ = _ := by simp only [FiniteLaw.map_mass]

end MatrixMultiplication.CompletionProductLaws

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Completion_ColorLaws
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype
attribute [-simp] _root_.OAI.MatrixMultiplication.CompletionTermination.retainedLeafEquiv_coordinates _root_.OAI.MatrixMultiplication.ConditionalLabels.normalizedCountLaw_mass _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_x _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_y _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_z
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

universe uCoord

namespace MatrixMultiplication.CompletionColorLaws

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels
open CompletionLaws CompletionProductLaws
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

variable {X Y Z : Type uCoord} [Fintype X] [Fintype Y] [Fintype Z]

theorem colorMix_map_mass {B : Type*} [Fintype B]
    (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) (f : Leaf S → B) (b : B) :
    ((colorMix S center output pc po α hα hα').map f).mass b =
      α * ((pc.map Subtype.val).map f).mass b +
        (1 - α) * ((po.map Subtype.val).map f).mass b := by
  rw [FiniteLaw.map_mass]
  simp only [colorMix_mass]
  calc
    _ = ∑ a, (α * (if f a = b then (pc.map Subtype.val).mass a else 0) +
        (1 - α) * (if f a = b then (po.map Subtype.val).mass a else 0)) := by
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        FiniteLaw.map_mass (pc.map Subtype.val) f b,
        FiniteLaw.map_mass (po.map Subtype.val) f b]

theorem colorMix_center_mass (S : FlaggedTensor X Y Z) (center output : Color)
    (hne : center ≠ output)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) (a : ColorSlice S center) :
    (colorMix S center output pc po α hα hα').mass a.val = α * pc.mass a := by
  rw [colorMix_mass, pc.map_mass_apply Subtype.val Subtype.val_injective,
    colorSlice_map_mass_zero S output po a.val (by simpa only [a.property] using hne)]
  ring

theorem conditionalCompletionLaw_mass
    (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (hm : 0 < m) (α : ℝ) (hα : 0 ≤ α) (hα' : α < 1)
    (a : ColorSlice (complete S center m) output) :
    (conditionalCompletionLaw S center output pc po m hm α hα hα').mass a =
      (iidColorLaw S center output pc po m α hα hα'.le).mass (slot S center m a.val) /
        eventMass (iidColorLaw S center output pc po m α hα hα'.le)
          (completionEvent S center output m) := by
  let e := conditionalLeafEquiv S center output m
  have he : e.symm (e a) = a := e.symm_apply_apply a
  conv_lhs => rw [← he]
  rw [conditionalCompletionLaw, transport_mass, condition_mass]
  rfl

end MatrixMultiplication.CompletionColorLaws

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Completion_CenterLaw
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype
attribute [-simp] _root_.OAI.MatrixMultiplication.CompletionTermination.retainedLeafEquiv_coordinates _root_.OAI.MatrixMultiplication.ConditionalLabels.normalizedCountLaw_mass _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_x _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_y _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_z
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

universe uCoord

namespace MatrixMultiplication.CompletionColorLaws

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels
open CompletionLaws CompletionProductLaws
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

variable {X Y Z : Type uCoord} [Fintype X] [Fintype Y] [Fintype Z]

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem centerCompletionEquiv_slots (S : FlaggedTensor X Y Z) (center : Color)
    (m : ℕ) (w : Fin m → ColorSlice S center) :
    slot S center m ((centerCompletionEquiv S center m) w).val =
      fun i => (w i).val := by
  funext i
  apply Subtype.ext
  rfl

theorem centerCompletionLaw_mass (S : FlaggedTensor X Y Z) (center : Color)
    (p : FiniteLaw (ColorSlice S center)) (m : ℕ) (w : Fin m → ColorSlice S center) :
    (centerCompletionLaw S center p m).mass ((centerCompletionEquiv S center m) w) =
      ∏ i, p.mass (w i) :=
  transport_mass (centerCompletionEquiv S center m) _ w

theorem centerCompletionLaw_entropy (S : FlaggedTensor X Y Z) (center : Color)
    (p : FiniteLaw (ColorSlice S center)) (m : ℕ) :
    finiteEntropy (centerCompletionLaw S center p m).mass =
      (m : ℝ) * finiteEntropy p.mass := by
  rw [centerCompletionLaw, transport_entropy, independentProduct_entropy]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem completionEvent_same_zero_mass (S : FlaggedTensor X Y Z) (center : Color)
    (p : FiniteLaw (ColorSlice S center)) (m : ℕ) :
    eventMass (iidColorLaw S center center p p m 0 (by norm_num) (by norm_num))
      (completionEvent S center center m) = 1 := by
  unfold eventMass
  rw [← (centerWordEquiv S center m).sum_comp
    (fun w => (iidColorLaw S center center p p m 0 (by norm_num) (by norm_num)).mass w.val)]
  calc
    _ = ∑ w : Fin m → ColorSlice S center,
        (independentProduct (fun _ : Fin m => p)).mass w := by
      apply Finset.sum_congr rfl
      intro w _
      change (∏ i, (colorMix S center center p p 0 (by norm_num) (by norm_num)).mass
        (w i).val) = ∏ i, p.mass (w i)
      apply Finset.prod_congr rfl
      intro i _
      rw [colorMix_mass]
      simp only [zero_mul, sub_zero, one_mul, zero_add]
      exact p.map_mass_apply Subtype.val Subtype.val_injective (w i)
    _ = 1 := (independentProduct (fun _ : Fin m => p)).total

theorem conditionalCompletionLaw_same_zero_mass
    (S : FlaggedTensor X Y Z) (center : Color)
    (p : FiniteLaw (ColorSlice S center)) (m : ℕ) (hm : 0 < m)
    (w : Fin m → ColorSlice S center) :
    (conditionalCompletionLaw S center center p p m hm 0 (by norm_num) (by norm_num)).mass
        ((centerCompletionEquiv S center m) w) = ∏ i, p.mass (w i) := by
  rw [conditionalCompletionLaw_mass, completionEvent_same_zero_mass, div_one,
    centerCompletionEquiv_slots]
  change (∏ i, (colorMix S center center p p 0 (by norm_num) (by norm_num)).mass
    (w i).val) = ∏ i, p.mass (w i)
  apply Finset.prod_congr rfl
  intro i _
  rw [colorMix_mass]
  simp only [zero_mul, sub_zero, one_mul, zero_add]
  exact p.map_mass_apply Subtype.val Subtype.val_injective (w i)

theorem conditionalCompletionLaw_same_zero_entropy
    (S : FlaggedTensor X Y Z) (center : Color)
    (p : FiniteLaw (ColorSlice S center)) (m : ℕ) (hm : 0 < m) :
    finiteEntropy
      (conditionalCompletionLaw S center center p p m hm 0 (by norm_num) (by norm_num)).mass =
      (m : ℝ) * finiteEntropy p.mass := by
  have hmass :
      (conditionalCompletionLaw S center center p p m hm 0 (by norm_num) (by norm_num)).mass =
        (centerCompletionLaw S center p m).mass := by
    funext a
    obtain ⟨w, rfl⟩ := (centerCompletionEquiv S center m).surjective a
    rw [conditionalCompletionLaw_same_zero_mass, centerCompletionLaw_mass]
  rw [hmass, centerCompletionLaw_entropy]

end MatrixMultiplication.CompletionColorLaws

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Completion_ColorEntropy
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype
attribute [-simp] _root_.OAI.MatrixMultiplication.CompletionTermination.retainedLeafEquiv_coordinates _root_.OAI.MatrixMultiplication.ConditionalLabels.normalizedCountLaw_mass _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_x _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_y _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_z
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

universe uCoord

namespace MatrixMultiplication.CompletionColorLaws

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

theorem finiteEntropy_scale {A : Type*} [Fintype A] (p : FiniteLaw A) (r : ℝ) :
    finiteEntropy (fun a => r * p.mass a) =
      entropyTerm r + r * finiteEntropy p.mass := by
  simp only [finiteEntropy, entropyTerm_mul, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, p.total, one_mul]

variable {X Y Z : Type uCoord} [Fintype X] [Fintype Y] [Fintype Z]

theorem colorMix_entropy (S : FlaggedTensor X Y Z) (center output : Color)
    (hne : center ≠ output)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) :
    finiteEntropy (colorMix S center output pc po α hα hα').mass =
      entropyTerm α + entropyTerm (1 - α) +
        α * finiteEntropy pc.mass + (1 - α) * finiteEntropy po.mass := by
  have hterm (a : Leaf S) :
      entropyTerm ((colorMix S center output pc po α hα hα').mass a) =
        entropyTerm (α * (pc.map Subtype.val).mass a) +
          entropyTerm ((1 - α) * (po.map Subtype.val).mass a) := by
    by_cases hc : leafColor S a = center
    · have ho : leafColor S a ≠ output := fun ho => hne (hc.symm.trans ho)
      rw [colorMix_mass, colorSlice_map_mass_zero S output po a ho]
      simp
    · rw [colorMix_mass, colorSlice_map_mass_zero S center pc a hc]
      simp
  calc
    finiteEntropy (colorMix S center output pc po α hα hα').mass =
        finiteEntropy (fun a => α * (pc.map Subtype.val).mass a) +
          finiteEntropy (fun a => (1 - α) * (po.map Subtype.val).mass a) := by
      simp only [finiteEntropy, hterm, Finset.sum_add_distrib]
    _ = _ := by
      rw [finiteEntropy_scale, finiteEntropy_scale,
        pc.map_entropy_of_injective Subtype.val Subtype.val_injective,
        po.map_entropy_of_injective Subtype.val Subtype.val_injective]
      ring

theorem iidColorLaw_entropy (S : FlaggedTensor X Y Z) (center output : Color)
    (hne : center ≠ output)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) :
    finiteEntropy (iidColorLaw S center output pc po m α hα hα').mass =
      (m : ℝ) * (entropyTerm α + entropyTerm (1 - α) +
        α * finiteEntropy pc.mass + (1 - α) * finiteEntropy po.mass) := by
  rw [iidColorLaw, CompletionProductLaws.independentProduct_entropy]
  simp only [colorMix_entropy S center output hne pc po α hα hα',
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end MatrixMultiplication.CompletionColorLaws

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Completion_Entropy
attribute [-simp] _root_.OAI.MatrixMultiplication.CompletionProductLaws.independentProduct_mass _root_.OAI.MatrixMultiplication.CompletionProductLaws.sigmaJoint_mass _root_.OAI.MatrixMultiplication.ConditionalLabels.normalizedCountLaw_mass _root_.OAI.MatrixMultiplication.Foundation.FiniteLabelHierarchy.prefixLaw_succ _root_.OAI.MatrixMultiplication.Foundation.FiniteLabelHierarchy.prefixLaw_succ_mass _root_.OAI.MatrixMultiplication.Foundation.FiniteLabelHierarchy.prefixLaw_zero_mass _root_.OAI.MatrixMultiplication.Foundation.RationalLaw.toFiniteLaw_mass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.CompletionLaws

open MatrixMultiplication.Foundation
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq

variable {A : Type*} [Fintype A]

theorem entropy_scaled_law (p : FiniteLaw A) (s : ℝ) :
    finiteEntropy (fun a => s * p.mass a) = entropyTerm s + s * finiteEntropy p.mass := by
  simp only [finiteEntropy, entropyTerm_mul, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, p.total, one_mul]

theorem mass_eq_event_mul_condition (p : FiniteLaw A) (P : A → Prop)
    (h : 0 < eventMass p P) (a : {a // P a}) :
    p.mass a.val = eventMass p P * (condition p P h).mass a := by
  rw [condition_mass, mul_div_cancel₀ _ h.ne']

theorem event_entropy (p : FiniteLaw A) (P : A → Prop)
    (h : 0 < eventMass p P) :
    (∑ a : {a // P a}, entropyTerm (p.mass a.val)) =
      entropyTerm (eventMass p P) + eventMass p P * finiteEntropy (condition p P h).mass := by
  conv_lhs => enter [2, a]; rw [mass_eq_event_mul_condition p P h a]
  exact entropy_scaled_law (condition p P h) (eventMass p P)

theorem condition_entropy_mul (p : FiniteLaw A) (P : A → Prop)
    (h : 0 < eventMass p P) :
    eventMass p P * finiteEntropy (condition p P h).mass =
      (∑ a : {a // P a}, entropyTerm (p.mass a.val)) - entropyTerm (eventMass p P) := by
  linarith [event_entropy p P h]

theorem eventMass_add_complement (p : FiniteLaw A) (P : A → Prop) :
    eventMass p P + eventMass p (fun a => ¬ P a) = 1 := by
  rw [eventMass, eventMass, sum_subtype_indicator, sum_subtype_indicator,
    ← Finset.sum_add_distrib]
  calc
    (∑ a, ((if P a then p.mass a else 0) + (if ¬ P a then p.mass a else 0))) =
        ∑ a, p.mass a := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : P a <;> simp [h]
    _ = _ := p.total

theorem entropy_sum_event_complement (p : FiniteLaw A) (P : A → Prop) :
    (∑ a : {a // P a}, entropyTerm (p.mass a.val)) +
      (∑ a : {a // ¬ P a}, entropyTerm (p.mass a.val)) = finiteEntropy p.mass := by
  rw [sum_subtype_indicator P (fun a => entropyTerm (p.mass a)),
    sum_subtype_indicator (fun a => ¬ P a) (fun a => entropyTerm (p.mass a)),
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : P a <;> simp [h]

theorem condition_entropy_of_removed_event (p : FiniteLaw A) (P : A → Prop)
    (hP : 0 < eventMass p P) (removedMass removedEntropy : ℝ)
    (hmass : eventMass p (fun a => ¬ P a) = removedMass)
    (hremoved : (∑ a : {a // ¬ P a}, entropyTerm (p.mass a.val)) =
      entropyTerm removedMass + removedMass * removedEntropy) :
    finiteEntropy (condition p P hP).mass =
      (finiteEntropy p.mass - entropyTerm removedMass -
        entropyTerm (1 - removedMass) - removedMass * removedEntropy) /
        (1 - removedMass) := by
  have hevent : eventMass p P = 1 - removedMass := by
    linarith [eventMass_add_complement p P]
  have hsum := entropy_sum_event_complement p P
  have hc := condition_entropy_mul p P hP
  rw [hremoved] at hsum
  rw [hevent] at hc
  apply (eq_div_iff (by linarith : 1 - removedMass ≠ 0)).mpr
  nlinarith

end MatrixMultiplication.CompletionLaws

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Completion_EntropyAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.CompletionEntropyAlgebra

open MatrixMultiplication.Foundation

private theorem conditionalMixEntropy_cancel
    (a C O L hc ho : ℝ) (m : ℕ)
    (hden : 1 - a ^ m ≠ 0)
    (hcLog : Real.log a = C - L)
    (hoLog : Real.log (1 - a) = O - L) :
    conditionalMixEntropy a m (C + hc) (O + ho) =
      m * L + Real.log (1 - a ^ m) +
        m * ((a - a ^ m) / (1 - a ^ m) * hc +
          (1 - a) / (1 - a ^ m) * ho) := by
  dsimp [conditionalMixEntropy, binaryEntropy, entropyTerm]
  rw [Real.log_pow, hcLog, hoLog]
  field_simp
  ring

private theorem ratio_range (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    0 < x / (x + y) ∧ x / (x + y) < 1 := by
  have hs : 0 < x + y := add_pos hx hy
  exact ⟨div_pos hx hs, (div_lt_one hs).mpr (by linarith)⟩

private theorem ratio_complement (x y : ℝ) (h : x + y ≠ 0) :
    1 - x / (x + y) = y / (x + y) := by
  field_simp
  exact add_sub_cancel_left x y

theorem binaryEntropy_cardinal_mixture (np nq : ℝ) (hnp : 0 < np) (hnq : 0 < nq) :
    let a := np / (np + nq)
    binaryEntropy a + a * Real.log np + (1 - a) * Real.log nq =
      Real.log (np + nq) := by
  let a := np / (np + nq)
  have hs : 0 < np + nq := add_pos hnp hnq
  have hcLog : Real.log a = Real.log np - Real.log (np + nq) :=
    Real.log_div hnp.ne' hs.ne'
  have hoLog : Real.log (1 - a) = Real.log nq - Real.log (np + nq) := by
    rw [show 1 - a = nq / (np + nq) from ratio_complement np nq hs.ne',
      Real.log_div hnq.ne' hs.ne']
  change binaryEntropy a + a * Real.log np + (1 - a) * Real.log nq = _
  dsimp [binaryEntropy, entropyTerm]
  rw [hcLog, hoLog]
  ring

theorem conditionalMixEntropy_incident
    (np nq hc ho : ℝ) (m : ℕ)
    (hnp : 0 < np) (hnq : 0 < nq) (hm : 0 < m) :
    let a := np / (np + nq)
    conditionalMixEntropy a m (Real.log np + hc) (Real.log nq + ho) -
        Real.log ((np + nq) ^ m - np ^ m) =
      m * ((a - a ^ m) / (1 - a ^ m) * hc +
        (1 - a) / (1 - a ^ m) * ho) := by
  let a := np / (np + nq)
  change conditionalMixEntropy a m (Real.log np + hc) (Real.log nq + ho) -
      Real.log ((np + nq) ^ m - np ^ m) = _
  have hs : 0 < np + nq := add_pos hnp hnq
  have ha : 0 < a ∧ a < 1 := ratio_range np nq hnp hnq
  have hden : 0 < 1 - a ^ m :=
    sub_pos.mpr (pow_lt_one₀ ha.1.le ha.2 (Nat.ne_of_gt hm))
  have hcLog : Real.log a = Real.log np - Real.log (np + nq) :=
    Real.log_div hnp.ne' hs.ne'
  have hoLog : Real.log (1 - a) = Real.log nq - Real.log (np + nq) := by
    rw [show 1 - a = nq / (np + nq) from ratio_complement np nq hs.ne',
      Real.log_div hnq.ne' hs.ne']
  have hfactor : (np + nq) ^ m - np ^ m =
      (np + nq) ^ m * (1 - a ^ m) := by
    dsimp [a]
    rw [div_pow]
    field_simp
  have hlog : Real.log ((np + nq) ^ m - np ^ m) =
      m * Real.log (np + nq) + Real.log (1 - a ^ m) := by
    rw [hfactor, Real.log_mul (pow_ne_zero _ hs.ne') hden.ne', Real.log_pow]
  rw [conditionalMixEntropy_cancel a (Real.log np) (Real.log nq)
    (Real.log (np + nq)) hc ho m hden.ne' hcLog hoLog, hlog]
  ring

theorem conditionalMixEntropy_gibbs (q hc ho : ℝ) (m : ℕ) (hm : 0 < m) :
    conditionalMixEntropy (Real.exp hc / (Real.exp hc + Real.exp ho)) m
        (Real.log q + hc) (Real.log q + ho) - m * Real.log q =
      Real.log ((Real.exp hc + Real.exp ho) ^ m - Real.exp ((m : ℝ) * hc)) := by
  let a := Real.exp hc / (Real.exp hc + Real.exp ho)
  have ha : 0 < a ∧ a < 1 := ratio_range _ _ (Real.exp_pos hc) (Real.exp_pos ho)
  have hden : 1 - a ^ m ≠ 0 :=
    (sub_pos.mpr (pow_lt_one₀ ha.1.le ha.2 (Nat.ne_of_gt hm))).ne'
  have hmean : m * ((a - a ^ m) / (1 - a ^ m) * Real.log q +
      (1 - a) / (1 - a ^ m) * Real.log q) = m * Real.log q := by
    field_simp
    ring
  have h := conditionalMixEntropy_incident (Real.exp hc) (Real.exp ho)
    (Real.log q) (Real.log q) m (Real.exp_pos hc) (Real.exp_pos ho) hm
  change conditionalMixEntropy a m (Real.log (Real.exp hc) + Real.log q)
      (Real.log (Real.exp ho) + Real.log q) -
      Real.log ((Real.exp hc + Real.exp ho) ^ m - Real.exp hc ^ m) =
        m * ((a - a ^ m) / (1 - a ^ m) * Real.log q +
          (1 - a) / (1 - a ^ m) * Real.log q) at h
  rw [Real.log_exp, Real.log_exp, add_comm hc (Real.log q),
    add_comm ho (Real.log q), hmean, ← Real.exp_nat_mul hc m] at h
  change conditionalMixEntropy a m (Real.log q + hc) (Real.log q + ho) -
      m * Real.log q = _
  linarith

end MatrixMultiplication.CompletionEntropyAlgebra

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_ComplexArithmetic_Growth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complex arithmetic programs and asymptotic matrix multiplication costs. -/

noncomputable section

namespace MatrixMultiplication.Foundation.Arithmetic

theorem exists_power_cover {b n : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) :
    ∃ k : ℕ, n ≤ b ^ k ∧ b ^ k ≤ b * n := by
  refine ⟨Nat.log b n + 1, (Nat.lt_pow_succ_log_self (by omega) n).le, ?_⟩
  rw [pow_succ']
  exact Nat.mul_le_mul_left b (Nat.pow_log_le_self b (by omega))

theorem geometric_cost_recurrence_bound (x : ℕ → ℝ) (a b d q : ℝ)
    (hx : 0 ≤ x 0) (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (haq : a < q) (hdq : d ≤ q)
    (hstep : ∀ k, x (k + 1) ≤ a * x k + b * d ^ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ k, x k ≤ C * q ^ k := by
  let C := x 0 + b / (q - a) + 1
  have hgap : 0 < q - a := sub_pos.mpr haq
  have hfrac : 0 ≤ b / (q - a) := div_nonneg hb hgap.le
  have hC : 0 < C := by dsimp [C] <;> linarith
  have hcancel : (q - a) * (b / (q - a)) = b := by
    field_simp [ne_of_gt hgap]
  have hCfrac : b / (q - a) ≤ C := by dsimp [C] <;> linarith
  have hcoeff : a * C + b ≤ C * q := by
    have hmul := mul_le_mul_of_nonneg_left hCfrac hgap.le
    rw [hcancel] at hmul
    calc
      a * C + b ≤ a * C + (q - a) * C := add_le_add_right hmul _
      _ = C * q := by ring
  refine ⟨C, hC, ?_⟩
  intro k
  induction k with
  | zero => simp only [pow_zero, mul_one]; dsimp [C] <;> linarith
  | succ k ih =>
    calc
      x (k + 1) ≤ a * x k + b * d ^ k := hstep k
      _ ≤ a * (C * q ^ k) + b * q ^ k :=
        add_le_add (mul_le_mul_of_nonneg_left ih ha)
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd hdq k) hb)
      _ = (a * C + b) * q ^ k := by ring
      _ ≤ (C * q) * q ^ k :=
        mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (hd.trans hdq) k)
      _ = C * q ^ (k + 1) := by rw [pow_succ]; ring

end MatrixMultiplication.Foundation.Arithmetic

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Entropy_ComplexAsymptoticRecurrence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

namespace MatrixMultiplication.Foundation

theorem affine_recurrence_shifted (x : ℕ → ℝ) (a c : ℝ) (ha : 0 ≤ a)
    (hstep : ∀ t, x (t + 1) ≤ a * x t + (a - 1) * c) :
    ∀ t, x t + c ≤ a ^ t * (x 0 + c) := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    calc
      x (t + 1) + c ≤ a * x t + (a - 1) * c + c := add_le_add_left (hstep t) c
      _ = a * (x t + c) := by ring
      _ ≤ a * (a ^ t * (x 0 + c)) := mul_le_mul_of_nonneg_left ih ha
      _ = a ^ (t + 1) * (x 0 + c) := by rw [pow_succ]; ring

theorem affine_recurrence_bound (x : ℕ → ℝ) (a b : ℝ) (ha : 1 < a) (hb : 0 ≤ b)
    (hstep : ∀ t, x (t + 1) ≤ a * x t + b) :
    ∀ t, x t ≤ a ^ t * (x 0 + b / (a - 1)) := by
  have hpos : 0 < a - 1 := sub_pos.mpr ha
  have hcancel : (a - 1) * (b / (a - 1)) = b := by
    field_simp [ne_of_gt hpos]
  have hshift := affine_recurrence_shifted x a (b / (a - 1)) (by linarith)
    (fun t => by rw [hcancel]; exact hstep t)
  intro t
  have hc : 0 ≤ b / (a - 1) := div_nonneg hb hpos.le
  exact (le_add_of_nonneg_right hc).trans (hshift t)

end MatrixMultiplication.Foundation

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Polynomial_ComplexPolynomialPowerGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial tensor restrictions and exact coefficient extraction. -/

noncomputable section

open Filter
open scoped Topology

namespace MatrixMultiplication.Foundation

theorem tendsto_affine_mul_geometric_zero (D C : ℝ) {q : ℝ}
    (hq : 0 ≤ q) (hq_one : q < 1) :
    Tendsto (fun n : ℕ => (D * (n : ℝ) + C) * q ^ n) atTop (𝓝 0) := by
  have hlinear := (tendsto_self_mul_const_pow_of_lt_one hq hq_one).const_mul D
  have hconstant := (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq_one).const_mul C
  simpa only [mul_zero, add_zero, add_mul, mul_assoc] using hlinear.add hconstant

theorem power_le_of_eventually_pow_le_affine_mul_pow {a r D C : ℝ}
    (hr : 0 ≤ r)
    (h : ∀ᶠ n : ℕ in atTop, a ^ n ≤ (D * (n : ℝ) + C) * r ^ n) :
    a ≤ r := by
  by_contra hnot
  have hra : r < a := lt_of_not_ge hnot
  have ha : 0 < a := hr.trans_lt hra
  have hratio : 0 ≤ r / a := div_nonneg hr ha.le
  have hratio_one : r / a < 1 := (div_lt_one ha).2 hra
  have hsmall :=
    (tendsto_affine_mul_geometric_zero D C hratio hratio_one).eventually_lt_const
      (show (0 : ℝ) < 1 from zero_lt_one)
  rcases (h.and hsmall).exists with ⟨n, hbound, hlt⟩
  have hge : (1 : ℝ) ≤ (D * (n : ℝ) + C) * (r / a) ^ n := by
    rw [div_pow, ← mul_div_assoc]
    exact (le_div_iff₀ (pow_pos ha n)).2 (by simpa only [one_mul] using hbound)
  exact (not_lt_of_ge hge) hlt

theorem power_le_of_forall_pow_le_affine_mul_pow {a r D C : ℝ}
    (hr : 0 ≤ r)
    (h : ∀ n : ℕ, 0 < n → a ^ n ≤ (D * (n : ℝ) + C) * r ^ n) :
    a ≤ r := by
  apply power_le_of_eventually_pow_le_affine_mul_pow hr
  exact eventually_atTop.2 ⟨1, fun n hn => h n (Nat.zero_lt_one.trans_le hn)⟩

theorem power_le_of_forall_pow_le_mul_pow {a r C : ℝ}
    (hr : 0 ≤ r) (h : ∀ n : ℕ, 0 < n → a ^ n ≤ C * r ^ n) :
    a ≤ r := by
  apply power_le_of_forall_pow_le_affine_mul_pow (D := 0) (C := C) hr
  simpa only [zero_mul, zero_add] using h

theorem power_le_of_forall_pow_le_linear_mul_pow (D : ℕ) {a r : ℝ}
    (hr : 0 ≤ r)
    (h : ∀ n : ℕ, 0 < n → a ^ n ≤ ((D * n + 1 : ℕ) : ℝ) * r ^ n) :
    a ≤ r := by
  apply power_le_of_forall_pow_le_affine_mul_pow (D := (D : ℝ)) (C := 1) hr
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] using h

end MatrixMultiplication.Foundation

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Tensor_ComplexBatchCeiling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

namespace MatrixMultiplication.Foundation

theorem le_batchCount_mul (R : ℕ) {k : ℕ} (hk : 0 < k) :
    R ≤ batchCount R k * k := by
  have hdiv := Nat.div_add_mod (R + k - 1) k
  have hmod := Nat.mod_lt (R + k - 1) hk
  rw [Nat.mul_comm k ((R + k - 1) / k)] at hdiv
  unfold batchCount
  omega

theorem batchCount_mul_lt (R : ℕ) {k : ℕ} (hk : 0 < k) :
    batchCount R k * k < R + k := by
  have hmul := Nat.div_mul_le_self (R + k - 1) k
  unfold batchCount
  omega

theorem batchCount_cast_lt (R : ℕ) {k : ℕ} (hk : 0 < k) :
    (batchCount R k : ℝ) < (R : ℝ) / (k : ℝ) + 1 := by
  have hkR : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hmul : (batchCount R k : ℝ) * (k : ℝ) < (R : ℝ) + (k : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_add] using
      (Nat.cast_lt (α := ℝ)).mpr (batchCount_mul_lt R hk)
  calc
    (batchCount R k : ℝ) < ((R : ℝ) + (k : ℝ)) / (k : ℝ) :=
      (lt_div_iff₀ hkR).mpr hmul
    _ = (R : ℝ) / (k : ℝ) + 1 := by rw [add_div, div_self (ne_of_gt hkR)]

theorem batchCount_cast_le (R : ℕ) {k : ℕ} (hk : 0 < k) :
    (batchCount R k : ℝ) ≤ (R : ℝ) / (k : ℝ) + 1 :=
  (batchCount_cast_lt R hk).le

theorem batchCount_mul_cast_le (R r : ℕ) {k : ℕ} (hk : 0 < k) :
    ((batchCount R k * r : ℕ) : ℝ) ≤
      (r : ℝ) / (k : ℝ) * (R : ℝ) + (r : ℝ) := by
  calc
    ((batchCount R k * r : ℕ) : ℝ) = (batchCount R k : ℝ) * (r : ℝ) := by
      rw [Nat.cast_mul]
    _ ≤ ((R : ℝ) / (k : ℝ) + 1) * (r : ℝ) :=
      mul_le_mul_of_nonneg_right (batchCount_cast_le R hk) (Nat.cast_nonneg r)
    _ = (r : ℝ) / (k : ℝ) * (R : ℝ) + (r : ℝ) := by
      simp only [div_eq_mul_inv]
      ring

theorem batchRank_succ_le_affine {k : ℕ} (hk : 0 < k) (r t : ℕ) :
    (batchRank k r (t + 1) : ℝ) ≤
      (r : ℝ) / (k : ℝ) * (batchRank k r t : ℝ) + (r : ℝ) := by
  rw [batchRank_succ]
  exact batchCount_mul_cast_le (batchRank k r t) r hk

namespace Tensor

variable {K X Y Z U V W A B : Type*} [CommSemiring K]

theorem RankAtMost.batch_product_ceiling [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor K X Y Z} {S : Tensor K U V W} {R k r : ℕ}
    (hT : RankAtMost T R)
    (hbatch : RankAtMost (directSum (fun _ : Fin k => S)) r) (hk : 0 < k) :
    RankAtMost (Tensor.product T S) (batchCount R k * r) :=
  hT.batch_product hbatch (le_batchCount_mul R hk)

end Tensor
end MatrixMultiplication.Foundation

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Tensor_ComplexTensorFlattening
attribute [-simp] _root_.OAI.MatrixMultiplication.Foundation.ExecutionPairingBudget.MatrixCoordinates.standard_tensor _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.ofRankAtMost_polynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {K X Y Z : Type*} [Field K]

theorem RankAtMost.card_le_of_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    {T : Tensor K X Y Z} {r : ℕ} (hT : RankAtMost T r)
    (x : ι → X) (y : ι → Y) (z : ι → Z)
    (hidentity : ∀ i j, T (x i) (y i) (z j) = if i = j then 1 else 0) :
    Fintype.card ι ≤ r := by
  rcases hT with ⟨a, b, c, heq⟩
  let L : Matrix ι (Fin r) K := fun i q => a q (x i) * b q (y i)
  let R : Matrix (Fin r) ι K := fun q j => c q (z j)
  have hmul : L * R = (1 : Matrix ι ι K) := by
    funext i j
    change (∑ q, (a q (x i) * b q (y i)) * c q (z j)) = if i = j then 1 else 0
    calc
      (∑ q, (a q (x i) * b q (y i)) * c q (z j)) = T (x i) (y i) (z j) :=
        (congrFun (congrFun (congrFun heq (x i)) (y i)) (z j)).symm
      _ = _ := hidentity i j
  have hle : (1 : Matrix ι ι K).rank ≤ r := by
    rw [← hmul]
    exact (Matrix.rank_mul_le_left L R).trans (by
      simpa only [Fintype.card_fin] using Matrix.rank_le_card_width L)
  simpa only [Matrix.rank_one] using hle

theorem directSum_matrixCoefficients_rank_lower
    {Label A B C : Type*} [Fintype Label] [Fintype A] [Fintype C]
    [DecidableEq Label] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [Nonempty B] {r : ℕ}
    (h : RankAtMost (directSum (fun _ : Label => matrixCoefficients (K := K) A B C)) r) :
    Fintype.card Label * (Fintype.card C * Fintype.card A) ≤ r := by
  classical
  let b₀ : B := Classical.choice inferInstance
  have hminor : ∀ i j : Label × (C × A),
      directSum (fun _ : Label => matrixCoefficients (K := K) A B C)
        (i.1, (i.2.2, b₀)) (i.1, (b₀, i.2.1)) j = if i = j then 1 else 0 := by
    intro i j
    simp only [directSum, matrixCoefficients]
    split_ifs <;> simp_all [Prod.ext_iff]
  have hlower := h.card_le_of_identity
    (fun i : Label × (C × A) => (i.1, (i.2.2, b₀)))
    (fun i : Label × (C × A) => (i.1, (b₀, i.2.1)))
    (fun i : Label × (C × A) => i) hminor
  simpa only [Fintype.card_prod] using hlower

end Tensor
end MatrixMultiplication.Foundation

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Tensor_ComplexEqualSummandASI
attribute [-simp] _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_auxiliaryRank _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_columns _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_inner _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_multiplicity _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_occurrences _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_rows _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_inner _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_multiplicity _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_outer _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_rank _root_.OAI.MatrixMultiplication.Foundation.CW75InitialExecution.execution_value _root_.OAI.MatrixMultiplication.Foundation.CW75Primitive.restriction_basePolynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.boundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.boundary_basePolynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.cyclicBoundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.twiceCyclicBoundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.ExecutionPairingBudget.MatrixCoordinates.scalar_tensor _root_.OAI.MatrixMultiplication.Foundation.ExecutionPairingBudget.MatrixCoordinates.standard_tensor _root_.OAI.MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution.cyclic_auxiliary _root_.OAI.MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution.onSupport_auxiliary _root_.OAI.MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution.onSupport_value _root_.OAI.MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution.reindexOriginal_auxiliary _root_.OAI.MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution.reindexOutput_auxiliary _root_.OAI.MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution.step_auxiliary _root_.OAI.MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution.swapXY_auxiliary _root_.OAI.MatrixMultiplication.Foundation.PolynomialLocalConstruction.kernel_constantMatrix_coeff_zero _root_.OAI.MatrixMultiplication.Foundation.PolynomialLocalConstruction.kernel_weightedCoordinatePolynomialMatrix_coeff_zero _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.cyclic_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.ofRankAtMost_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.product_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.pullback_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.restrict_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialRestrictionDegeneration.compose_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.restrictPolynomial_coeff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

noncomputable section

namespace MatrixMultiplication.Foundation

namespace Tensor

theorem matrixCoefficients_fin_one_rank {K : Type*} [CommSemiring K] :
    RankAtMost (matrixCoefficients (K := K) (Fin 1) (Fin 1) (Fin 1)) 1 := by
  have heq : matrixCoefficients (K := K) (Fin 1) (Fin 1) (Fin 1) =
      rankOne (fun _ => 1) (fun _ => 1) (fun _ => 1) := by
    funext x y z
    have hxy : x.2 = y.1 := Subsingleton.elim _ _
    have hyz : y.2 = z.1 := Subsingleton.elim _ _
    have hzx : z.2 = x.1 := Subsingleton.elim _ _
    simp [matrixCoefficients, rankOne, hxy, hyz, hzx]
  rw [heq]
  exact rankOne_rankAtMost _ _ _

end Tensor

end MatrixMultiplication.Foundation

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Completion_FiniteRealization
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionLabels.leafFintype _root_.OAI.MatrixMultiplication.CompletionLabels.retainedLeafFintype _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.CompletionFiniteRealization

open MatrixMultiplication.Foundation RecursiveCompletion
open scoped BigOperators Classical

theorem power_coefficient_one {X Y Z : Type*} (T : Tensor ℂ X Y Z)
    (unit : ∀ x y z, T x y z ≠ 0 → T x y z = 1) (n : ℕ)
    (x : Fin n → X) (y : Fin n → Y) (z : Fin n → Z)
    (supported : Tensor.power T n x y z ≠ 0) : Tensor.power T n x y z = 1 := by
  apply Finset.prod_eq_one
  intro i hi
  exact unit _ _ _ ((Finset.prod_ne_zero_iff.mp supported) i hi)

theorem complete_coefficient_one {X Y Z : Type*} (S : FlaggedTensor X Y Z)
    (unit : ∀ x y z, S.tensor x y z ≠ 0 → S.tensor x y z = 1)
    (center : Color) (m : ℕ) (x : Fin m → X) (y : Fin m → Y) (z : Fin m → Z)
    (supported : (complete S center m).tensor x y z ≠ 0) :
    (complete S center m).tensor x y z = 1 := by
  rw [complete_tensor] at supported ⊢
  split_ifs at supported ⊢ with hweight
  · exact power_coefficient_one S.tensor unit m x y z supported
  · exact False.elim (supported rfl)

theorem script_coefficient_one {X Y Z : Type*} (S : FlaggedTensor X Y Z)
    (unit : ∀ x y z, S.tensor x y z ≠ 0 → S.tensor x y z = 1) (s : Script) :
    ∀ x y z, (s.tensor S).tensor x y z ≠ 0 → (s.tensor S).tensor x y z = 1 := by
  induction s with
  | base => exact unit
  | step prior center m ih => exact complete_coefficient_one (prior.tensor S) ih center m

open CompletionHierarchyWords CompletionExecution ExecutionPairingBudget

end MatrixMultiplication.CompletionFiniteRealization

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Completion_HierarchyPrograms
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.CompletionHierarchyWords

open MatrixMultiplication.Foundation

universe u v p q

variable {A : Type u}

namespace ReadableHierarchy

open RecursiveCompletion CompletionLabels.TopologicalFlatten

theorem ofProgram_complete {Coord : Color → Type v} {Context : Type q} {Code : Type p}
    [Fintype Code] {depth : ℕ} (s : Program A Coord Context Code depth)
    (ctx : Context) (hctx : ∀ a, s.context a = ctx)
    (joint : Function.Injective (fun a => (s.view .B a, s.view .C a, s.view .A a)))
    (complete : s.Complete) :
    Function.Injective (labelRecordOf (ofProgram s ctx hctx joint).labels depth) := by
  intro a b h
  apply complete a b ((hctx a).trans (hctx b).symm)
  intro n hn
  exact label_eq_of_record_eq s.labels h hn

end ReadableHierarchy

end MatrixMultiplication.CompletionHierarchyWords

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Completion_Partitions
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionLabels.leafFintype _root_.OAI.MatrixMultiplication.CompletionLabels.retainedLeafFintype _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype
attribute [-simp] _root_.OAI.MatrixMultiplication.CompletionLabels.rootColor_rootIndex _root_.OAI.MatrixMultiplication.CompletionLabels.slot_packLeaf _root_.OAI.MatrixMultiplication.CompletionLabels.terminationProgram_context _root_.OAI.MatrixMultiplication.CompletionLabels.terminationProgram_view _root_.OAI.MatrixMultiplication.CompletionTermination.retainedLeafEquiv_coordinates _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_x _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_y _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_z
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.CompletionPartitions

open MatrixMultiplication.Foundation RecursiveCompletion
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

variable {X Y Z : Type*} [Fintype X]

theorem partition_count (S : FlaggedTensor X Y Z) :
    activeCount S + inactiveCount S = Fintype.card X := by
  rw [activeCount, inactiveCount, Fintype.card_subtype_compl]
  exact Nat.add_sub_of_le (Fintype.card_subtype_le S.flagB)

theorem card_all (p : X → Prop) (m : ℕ) :
    Fintype.card {x : Fin m → X // ∀ i, p (x i)} = Fintype.card {x // p x} ^ m := by
  calc
    _ = Fintype.card (Fin m → {x // p x}) :=
      Fintype.card_congr Equiv.subtypePiEquivPi
    _ = _ := by simp

theorem activeCount_minus (S : FlaggedTensor X Y Z) (m : ℕ) :
    activeCount (complete S .B m) = activeCount S ^ m := by
  simpa [activeCount, complete, flagB, raisedFlag] using card_all S.flagB m

theorem inactiveCount_plus (S : FlaggedTensor X Y Z) (center : Color)
    (hc : center ≠ .B) (m : ℕ) :
    inactiveCount (complete S center m) = inactiveCount S ^ m := by
  change Fintype.card {x : Fin m → X // ¬ raisedFlag center .B (fun i => S.flagB (x i))} = _
  calc
    _ = Fintype.card {x : Fin m → X // ∀ i, ¬ S.flagB (x i)} :=
      Fintype.card_congr (Equiv.subtypeEquivRight fun x => by simp [raisedFlag, hc])
    _ = Fintype.card (Fin m → {x // ¬ S.flagB x}) :=
      Fintype.card_congr
        { toFun := fun w i => ⟨w.val i, w.property i⟩
          invFun := fun w => ⟨fun i => (w i).val, fun i => (w i).property⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    _ = _ := by simp [inactiveCount]

theorem fraction_sum [Nonempty X] (S : FlaggedTensor X Y Z) :
    activeFraction S + inactiveFraction S = 1 := by
  have hc : (Fintype.card X : ℝ) ≠ 0 := (Nat.cast_pos.mpr Fintype.card_pos).ne'
  rw [activeFraction, inactiveFraction, ← add_div, ← Nat.cast_add, partition_count]
  exact div_self hc

theorem activeFraction_minus (S : FlaggedTensor X Y Z) (m : ℕ) :
    activeFraction (complete S .B m) = activeFraction S ^ m := by
  simp only [activeFraction, activeCount_minus, Fintype.card_fun,
    Fintype.card_fin, Nat.cast_pow, div_pow]

theorem inactiveFraction_plus (S : FlaggedTensor X Y Z) (center : Color)
    (hc : center ≠ .B) (m : ℕ) :
    inactiveFraction (complete S center m) = inactiveFraction S ^ m := by
  simp only [inactiveFraction, inactiveCount_plus S center hc m,
    Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, div_pow]

theorem activeFraction_plus [Nonempty X] (S : FlaggedTensor X Y Z)
    (center : Color) (hc : center ≠ .B) (m : ℕ) :
    activeFraction (complete S center m) = 1 - (1 - activeFraction S) ^ m := by
  have h := fraction_sum (complete S center m)
  rw [inactiveFraction_plus S center hc m] at h
  have hold : inactiveFraction S = 1 - activeFraction S := by
    linarith [fraction_sum S]
  rw [hold] at h
  linarith

end MatrixMultiplication.CompletionPartitions

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Completion_ProgramPrefixes
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.labelRecordZero_subsingleton
attribute [-simp] _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_auxiliaryRank _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_columns _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_inner _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_multiplicity _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_occurrences _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_rows _root_.OAI.MatrixMultiplication.CompletionTermination.retainedLeafEquiv_coordinates _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_inner _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_multiplicity _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_outer _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_rank _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_x _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_y _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_z _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.appendCode_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.appendPrefix_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.decodedFine_eq_geometryDecode _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.encodeSourceWord_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.finePrefix_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.mem_conditionalFinset _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.oldPrefix_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.rootPrefixWord_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourcePrefixEquiv_apply_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourcePrefixEquiv_symm_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourceSymbol_encodeSourceWord _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourceSymbol_record
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.CompletionLabels.TopologicalFlatten

open MatrixMultiplication.Foundation RecursiveCompletion

universe u v w z

theorem labelRecordOf_eq_iff {A : Type u} {Label : ℕ → Type v}
    (labels : ∀ n, A → Label n) (n : ℕ) (a b : A) :
    labelRecordOf labels n a = labelRecordOf labels n b ↔
      ∀ k, k < n → labels k a = labels k b := by
  constructor
  · intro h k hk
    exact label_eq_of_record_eq labels h hk
  · intro h
    revert h
    induction n with
    | zero => intro h; rfl
    | succ n ih =>
        intro h
        apply Prod.ext
        · exact ih (fun k hk => h k (Nat.lt_succ_of_lt hk))
        · exact h n (Nat.lt_succ_self n)

namespace Program

variable {A : Type u} {Coord : Color → Type v}
  {Context OtherContext : Type z} {Code : Type w} {d e : ℕ}

theorem append_record_eq_iff
    (p : Program A Coord Context Code d) (q : Program A Coord OtherContext Code e)
    (sameView : ∀ side a, p.view side a = q.view side a)
    (derive : Context → (Fin d → Code) → OtherContext)
    (derive_correct : ∀ a, derive (p.context a) (fun j => p.labels j.val a) = q.context a)
    (k : ℕ) (a b : A) :
    labelRecordOf (p.append q sameView derive derive_correct).labels (d + k) a =
        labelRecordOf (p.append q sameView derive derive_correct).labels (d + k) b ↔
      labelRecordOf p.labels d a = labelRecordOf p.labels d b ∧
        labelRecordOf q.labels k a = labelRecordOf q.labels k b := by
  simp only [labelRecordOf_eq_iff]
  constructor
  · intro h
    constructor
    · intro n hn
      have heq := h n (by omega)
      simpa only [append_labels_left p q sameView derive derive_correct n hn] using heq
    · intro n hn
      have heq := h (d + n) (by omega)
      simpa only [append_labels_right] using heq
  · rintro ⟨hp, hq⟩ n hn
    by_cases hd : n < d
    · simpa only [append_labels_left p q sameView derive derive_correct n hd] using hp n hd
    · have hdn : d + (n - d) = n := Nat.add_sub_of_le (Nat.le_of_not_gt hd)
      have heq := hq (n - d) (by omega)
      have ha := append_labels_right p q sameView derive derive_correct (n - d) a
      have hb := append_labels_right p q sameView derive derive_correct (n - d) b
      rw [hdn] at ha hb
      exact ha.trans (heq.trans hb.symm)

theorem recode_record_eq_iff {NewCode : Type*}
    (p : Program A Coord Context Code d) (encode : Code → NewCode)
    (decode : NewCode → Code) (roundtrip : Function.LeftInverse decode encode)
    (k : ℕ) (a b : A) :
    labelRecordOf (p.recode encode decode roundtrip).labels k a =
        labelRecordOf (p.recode encode decode roundtrip).labels k b ↔
      labelRecordOf p.labels k a = labelRecordOf p.labels k b := by
  simp only [labelRecordOf_eq_iff]
  constructor
  · intro h n hn
    exact roundtrip.injective (h n hn)
  · intro h n hn
    exact congrArg encode (h n hn)

theorem pow_record_eq_iff [Inhabited Code]
    (p : Program A Coord Context Code d) (m : ℕ) (i : Fin m)
    (k : ℕ) (hk : k ≤ d) (a b : Fin m → A) :
    labelRecordOf (p.pow m).labels (i.val * d + k) a =
        labelRecordOf (p.pow m).labels (i.val * d + k) b ↔
      (∀ j : Fin m, j.val < i.val →
        labelRecordOf p.labels d (a j) = labelRecordOf p.labels d (b j)) ∧
      labelRecordOf p.labels k (a i) = labelRecordOf p.labels k (b i) := by
  simp only [labelRecordOf_eq_iff]
  constructor
  · intro h
    constructor
    · intro j hj n hn
      have hindex : j.val * d + n < i.val * d + k := by
        calc
          j.val * d + n < j.val * d + d := Nat.add_lt_add_left hn _
          _ = (j.val + 1) * d := by rw [Nat.add_mul, Nat.one_mul]
          _ ≤ i.val * d := Nat.mul_le_mul_right d (Nat.succ_le_of_lt hj)
          _ ≤ i.val * d + k := Nat.le_add_right _ _
      have heq := h (j.val * d + n) hindex
      simpa only [pow_labels p m a j n hn, pow_labels p m b j n hn] using heq
    · intro n hn
      have hnd : n < d := lt_of_lt_of_le hn hk
      have heq := h (i.val * d + n) (Nat.add_lt_add_left hn _)
      simpa only [pow_labels p m a i n hnd, pow_labels p m b i n hnd] using heq
  · rintro ⟨hp, hc⟩ n hn
    have hd : 0 < d := by
      by_contra h
      have hz : d = 0 := by omega
      simp [hz] at hk hn
      omega
    have hq : n / d ≤ i.val := by
      have hbound : n < (i.val + 1) * d := by
        rw [Nat.add_mul, Nat.one_mul]
        exact lt_of_lt_of_le hn (Nat.add_le_add_left hk _)
      exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hd).2 hbound)
    let j : Fin m := ⟨n / d, lt_of_le_of_lt hq i.isLt⟩
    have hrem : n % d < d := Nat.mod_lt n hd
    have hsplit : j.val * d + n % d = n := by
      simpa only [j, Nat.mul_comm] using Nat.div_add_mod n d
    have heq : p.labels (n % d) (a j) = p.labels (n % d) (b j) := by
      by_cases hj : j.val < i.val
      · exact hp j hj (n % d) hrem
      · have hji : j = i := Fin.ext (by dsimp [j] at hj ⊢; omega)
        have hcur : n % d < k := by
          rw [hji] at hsplit
          omega
        simpa only [hji] using hc (n % d) hcur
    rw [← hsplit, pow_labels p m a j (n % d) hrem, pow_labels p m b j (n % d) hrem]
    exact heq

end Program
end MatrixMultiplication.CompletionLabels.TopologicalFlatten

namespace MatrixMultiplication.CompletionLabels

open MatrixMultiplication.Foundation RecursiveCompletion TopologicalFlatten

attribute [local instance] Classical.propDecidable Classical.decEq

universe uCoord
variable {X Y Z : Type uCoord}

theorem completionLocalProgram_label_root {Code : Type*} [Inhabited Code] {depth : ℕ}
    (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (context_eq : ∀ a, p.context a = leafColor S a)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side)
    (n : ℕ) (hn : n < 3) (a : Leaf (complete S center m)) :
    (completionLocalProgram S center m p context_eq view_eq).labels n a =
      encodePattern (if leafColor (complete S center m) a = rootColor n then
        some (pattern S center m a) else none) := by
  change (if n < 3 then encodePattern ((patternProgram S center m).labels n a)
    else (inheritedProgram S center m p view_eq).labels (n - 3) a) = _
  rw [ite_eq_left hn]
  rfl

theorem completionLocalProgram_pair_root {Code : Type*} [Inhabited Code] {depth : ℕ}
    (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (context_eq : ∀ a, p.context a = leafColor S a)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side)
    (n : ℕ) (hn : n < 3) :
    (completionLocalProgram S center m p context_eq view_eq).pair n =
      ownerPair center (rootColor n) := by
  change (if n < 3 then ownerPair center (rootColor n) else p.pair ((n - 3) % depth)) = _
  rw [ite_eq_left hn]

theorem completionLocalProgram_label_slot {Code : Type*} [Inhabited Code] {depth : ℕ}
    (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (context_eq : ∀ a, p.context a = leafColor S a)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side)
    (i : Fin m) (k : ℕ) (hk : k < depth) (a : Leaf (complete S center m)) :
    (completionLocalProgram S center m p context_eq view_eq).labels (3 + (i.val * depth + k)) a =
      encodeOld (p.labels k (slot S center m a i)) := by
  change (if 3 + (i.val * depth + k) < 3 then
    encodePattern ((patternProgram S center m).labels (3 + (i.val * depth + k)) a)
    else (inheritedProgram S center m p view_eq).labels
      (3 + (i.val * depth + k) - 3) a) = _
  have hsub : 3 + (i.val * depth + k) - 3 = i.val * depth + k := by omega
  rw [ite_eq_right (by omega), hsub]
  change ((p.recode encodeOld decodeOld oldCode_roundtrip).pow m).labels
    (i.val * depth + k) (slot S center m a) = _
  rw [Program.pow_labels _ m _ i k hk]
  rfl

theorem completionLocalProgram_pair_slot {Code : Type*} [Inhabited Code] {depth : ℕ}
    (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (context_eq : ∀ a, p.context a = leafColor S a)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side)
    (i : Fin m) (k : ℕ) (hk : k < depth) :
    (completionLocalProgram S center m p context_eq view_eq).pair (3 + (i.val * depth + k)) =
      p.pair k := by
  change (if 3 + (i.val * depth + k) < 3 then _
    else p.pair ((3 + (i.val * depth + k) - 3) % depth)) = _
  rw [ite_eq_right (by omega)]
  have hsub : 3 + (i.val * depth + k) - 3 = i.val * depth + k := by omega
  rw [hsub, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hk]

theorem patternProgram_record_eq_iff (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (a b : Leaf (complete S center m)) :
    labelRecordOf (patternProgram S center m).labels 3 a =
        labelRecordOf (patternProgram S center m).labels 3 b ↔
      leafColor (complete S center m) a = leafColor (complete S center m) b ∧
        pattern S center m a = pattern S center m b := by
  constructor
  · intro h
    have heq := label_eq_of_record_eq (patternProgram S center m).labels h
      (rootIndex (leafColor (complete S center m) a)).isLt
    change (if leafColor (complete S center m) a =
        rootColor (rootIndex (leafColor (complete S center m) a)).val
      then some (pattern S center m a) else none) =
      (if leafColor (complete S center m) b =
        rootColor (rootIndex (leafColor (complete S center m) a)).val
      then some (pattern S center m b) else none) at heq
    rw [rootColor_rootIndex, ite_eq_left rfl] at heq
    by_cases hb : leafColor (complete S center m) b = leafColor (complete S center m) a
    · rw [ite_eq_left hb] at heq
      exact ⟨hb.symm, Option.some.inj heq⟩
    · rw [ite_eq_right hb] at heq
      cases heq
  · rintro ⟨hc, hp⟩
    apply (labelRecordOf_eq_iff _ _ _ _).mpr
    intro n hn
    change (if leafColor (complete S center m) a = rootColor n then
      some (pattern S center m a) else none) =
      (if leafColor (complete S center m) b = rootColor n then
      some (pattern S center m b) else none)
    rw [hc, hp]

theorem completionProgram_record_eq_iff {Code : Type*} [Inhabited Code] {depth : ℕ}
    (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (context_eq : ∀ a, p.context a = leafColor S a)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side)
    (i : Fin m) (k : ℕ) (hk : k ≤ depth)
    (a b : Leaf (complete S center m)) :
    labelRecordOf (completionLocalProgram S center m p context_eq view_eq).labels
        (3 + (i.val * depth + k)) a =
      labelRecordOf (completionLocalProgram S center m p context_eq view_eq).labels
        (3 + (i.val * depth + k)) b ↔
      (leafColor (complete S center m) a = leafColor (complete S center m) b ∧
        pattern S center m a = pattern S center m b) ∧
      ((∀ j : Fin m, j.val < i.val →
        labelRecordOf p.labels depth (slot S center m a j) =
          labelRecordOf p.labels depth (slot S center m b j)) ∧
        labelRecordOf p.labels k (slot S center m a i) =
          labelRecordOf p.labels k (slot S center m b i)) := by
  change labelRecordOf (completionProgram S center m p context_eq view_eq).labels
      (3 + (i.val * depth + k)) a =
    labelRecordOf (completionProgram S center m p context_eq view_eq).labels
      (3 + (i.val * depth + k)) b ↔ _
  trans
    (labelRecordOf ((patternProgram S center m).recode (encodePattern (Code := Code))
        decodePatternCode patternCode_roundtrip).labels 3 a =
      labelRecordOf ((patternProgram S center m).recode (encodePattern (Code := Code))
        decodePatternCode patternCode_roundtrip).labels 3 b ∧
      labelRecordOf (inheritedProgram S center m p view_eq).labels (i.val * depth + k) a =
        labelRecordOf (inheritedProgram S center m p view_eq).labels (i.val * depth + k) b)
  · exact Program.append_record_eq_iff _ _ _ _ _ (i.val * depth + k) a b
  rw [Program.recode_record_eq_iff, patternProgram_record_eq_iff]
  have htail :
      (labelRecordOf (inheritedProgram S center m p view_eq).labels (i.val * depth + k) a =
        labelRecordOf (inheritedProgram S center m p view_eq).labels (i.val * depth + k) b) ↔
      (labelRecordOf ((p.recode (encodeOld (m := m)) decodeOld oldCode_roundtrip).pow m).labels
        (i.val * depth + k) (slot S center m a) =
        labelRecordOf ((p.recode (encodeOld (m := m)) decodeOld oldCode_roundtrip).pow m).labels
          (i.val * depth + k) (slot S center m b)) := by
    simp only [labelRecordOf_eq_iff]
    rfl
  rw [htail, Program.pow_record_eq_iff _ m i k hk]
  simp only [Program.recode_record_eq_iff]

end MatrixMultiplication.CompletionLabels

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Tensor_UniformCoordinate
attribute [-simp] _root_.OAI.MatrixMultiplication.CompletionProductLaws.independentProduct_mass _root_.OAI.MatrixMultiplication.CompletionProductLaws.sigmaJoint_mass _root_.OAI.MatrixMultiplication.ConditionalLabels.normalizedCountLaw_mass _root_.OAI.MatrixMultiplication.Foundation.FiniteLabelHierarchy.prefixLaw_succ _root_.OAI.MatrixMultiplication.Foundation.FiniteLabelHierarchy.prefixLaw_succ_mass _root_.OAI.MatrixMultiplication.Foundation.FiniteLabelHierarchy.prefixLaw_zero_mass _root_.OAI.MatrixMultiplication.Foundation.RationalLaw.toFiniteLaw_mass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

noncomputable section

namespace MatrixMultiplication.CompletionLaws

open MatrixMultiplication.Foundation
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq

variable {A X : Type*} [Fintype A] [Fintype X]

theorem uniform_coordinate_entropy (p : FiniteLaw A) (f : A → X) (P : X → Prop)
    (h : UniformCoordinate p f P) :
    finiteEntropy (p.map f).mass = Real.log (Fintype.card {x // P x}) := by
  calc
    _ = ∑ x, if P x then entropyTerm (Fintype.card {x // P x} : ℝ)⁻¹ else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [h x]
      split_ifs <;> simp
    _ = ∑ _x : {x // P x}, entropyTerm (Fintype.card {x // P x} : ℝ)⁻¹ :=
      (sum_subtype_indicator P _).symm
    _ = _ := finiteEntropy_uniform

theorem uniform_coordinate_eventMass (p : FiniteLaw A) (f : A → X)
    (P Q : X → Prop) (h : UniformCoordinate p f P) :
    eventMass p (fun a => Q (f a)) =
      (Fintype.card {x // P x ∧ Q x} : ℝ) / Fintype.card {x // P x} := by
  rw [eventMass_coordinate]
  unfold eventMass
  have hmass : (∑ x : {x // Q x}, (p.map f).mass x.val) =
      ∑ x : {x // Q x}, if P x.val then (Fintype.card {x // P x} : ℝ)⁻¹ else 0 := by
    apply Finset.sum_congr rfl
    intro x _
    exact h x.val
  rw [hmass, sum_subtype_indicator Q
    (fun x => if P x then (Fintype.card {x // P x} : ℝ)⁻¹ else 0)]
  have hsum : (∑ x, if Q x then
      (if P x then (Fintype.card {x // P x} : ℝ)⁻¹ else 0) else 0) =
      ∑ x, if P x ∧ Q x then (Fintype.card {x // P x} : ℝ)⁻¹ else 0 := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hp : P x <;> by_cases hq : Q x <;> simp [hp, hq]
  rw [hsum, ← sum_subtype_indicator (fun x => P x ∧ Q x)
    (fun _ => (Fintype.card {x // P x} : ℝ)⁻¹)]
  simp [div_eq_mul_inv]

theorem uniform_coordinate_condition (p : FiniteLaw A) (f : A → X)
    (P Q : X → Prop) (h : UniformCoordinate p f P)
    (hP : 0 < Fintype.card {x // P x})
    (hPQ : 0 < Fintype.card {x // P x ∧ Q x}) :
    ∃ hevent : 0 < eventMass p (fun a => Q (f a)),
      UniformCoordinate (condition p (fun a => Q (f a)) hevent)
        (fun a => f a.val) (fun x => P x ∧ Q x) := by
  have hP' : (0 : ℝ) < Fintype.card {x // P x} := Nat.cast_pos.mpr hP
  have hPQ' : (0 : ℝ) < Fintype.card {x // P x ∧ Q x} := Nat.cast_pos.mpr hPQ
  have hevent : 0 < eventMass p (fun a => Q (f a)) := by
    rw [uniform_coordinate_eventMass p f P Q h]
    exact div_pos hPQ' hP'
  refine ⟨hevent, fun x => ?_⟩
  rw [condition_coordinate_mass, h x, uniform_coordinate_eventMass p f P Q h]
  by_cases hp : P x <;> by_cases hq : Q x <;> simp [hp, hq]
  rw [div_div_eq_mul_div, inv_mul_cancel₀ hP'.ne', one_div]

end MatrixMultiplication.CompletionLaws

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Entropy_IndependentConditioning
attribute [-simp] _root_.OAI.MatrixMultiplication.CompletionProductLaws.independentProduct_mass _root_.OAI.MatrixMultiplication.CompletionProductLaws.sigmaJoint_mass _root_.OAI.MatrixMultiplication.ConditionalLabels.normalizedCountLaw_mass _root_.OAI.MatrixMultiplication.Foundation.FiniteLabelHierarchy.prefixLaw_succ _root_.OAI.MatrixMultiplication.Foundation.FiniteLabelHierarchy.prefixLaw_succ_mass _root_.OAI.MatrixMultiplication.Foundation.FiniteLabelHierarchy.prefixLaw_zero_mass _root_.OAI.MatrixMultiplication.Foundation.RationalLaw.toFiniteLaw_mass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

namespace MatrixMultiplication.CompletionLaws

open MatrixMultiplication.Foundation
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq

variable {A B X : Type*} [Fintype A] [Fintype B] [Fintype X]

theorem condition_map_mass (p : FiniteLaw A) (P : A → Prop)
    (h : 0 < eventMass p P) (f : A → X) (x : X) :
    ((condition p P h).map (fun a => f a.val)).mass x =
      (∑ a : {a // P a}, if f a.val = x then p.mass a.val else 0) / eventMass p P := by
  rw [FiniteLaw.map_mass, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  rw [condition_mass]
  split_ifs <;> simp

theorem joint_event_sum (p : FiniteLaw A) (f : A → X) (g : A → B)
    (Q : B → Prop) (x : X) :
    (∑ a : {a // Q (g a)}, if f a.val = x then p.mass a.val else 0) =
      ∑ b : {b // Q b}, (p.map (fun a => (f a, g a))).mass (x, b.val) := by
  rw [sum_subtype_indicator (fun a => Q (g a))
    (fun a => if f a = x then p.mass a else 0),
    sum_subtype_indicator Q
      (fun b => (p.map (fun a => (f a, g a))).mass (x, b))]
  simp only [FiniteLaw.map_mass, Prod.mk.injEq]
  calc
    (∑ a, if Q (g a) then (if f a = x then p.mass a else 0) else 0) =
        ∑ a, ∑ b, if Q b then (if f a = x ∧ g a = b then p.mass a else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_eq_single (g a)]
      · simp
      · intro b _ hb
        simp [Ne.symm hb]
      · simp
    _ = ∑ b, ∑ a, if Q b then (if f a = x ∧ g a = b then p.mass a else 0) else 0 :=
      Finset.sum_comm
    _ = ∑ b, if Q b then ∑ a, if f a = x ∧ g a = b then p.mass a else 0 else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      split_ifs <;> simp

theorem condition_independent_coordinate_mass (p : FiniteLaw A)
    (f : A → X) (g : A → B) (Q : B → Prop)
    (independent : ∀ x b, (p.map (fun a => (f a, g a))).mass (x, b) =
      (p.map f).mass x * (p.map g).mass b)
    (h : 0 < eventMass p (fun a => Q (g a))) (x : X) :
    ((condition p (fun a => Q (g a)) h).map (fun a => f a.val)).mass x =
      (p.map f).mass x := by
  rw [condition_map_mass, joint_event_sum]
  simp_rw [independent]
  rw [← Finset.mul_sum]
  change ((p.map f).mass x * eventMass (p.map g) Q) /
      eventMass p (fun a => Q (g a)) = _
  rw [← eventMass_coordinate p g Q, mul_div_cancel_right₀ _ h.ne']

theorem uniform_coordinate_independent_condition (p : FiniteLaw A)
    (f : A → X) (g : A → B) (P : X → Prop) (Q : B → Prop)
    (uniform : UniformCoordinate p f P)
    (independent : ∀ x b, (p.map (fun a => (f a, g a))).mass (x, b) =
      (p.map f).mass x * (p.map g).mass b)
    (h : 0 < eventMass p (fun a => Q (g a))) :
    UniformCoordinate (condition p (fun a => Q (g a)) h)
      (fun a => f a.val) P := by
  intro x
  rw [condition_independent_coordinate_mass p f g Q independent h]
  exact uniform x

end MatrixMultiplication.CompletionLaws

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Completion_TerminationLaw
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype
attribute [-simp] _root_.OAI.MatrixMultiplication.CompletionTermination.retainedLeafEquiv_coordinates _root_.OAI.MatrixMultiplication.ConditionalLabels.normalizedCountLaw_mass _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_x _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_y _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_z
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.CompletionTerminationLaw

open MatrixMultiplication.Foundation CompletionLabels CompletionColorLaws CompletionLaws
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

universe u
variable {X Y Z : Type u} [Fintype X] [Fintype Y] [Fintype Z]

theorem law_mass (S : FlaggedTensor X Y Z) (first second : Color)
    (pf : FiniteLaw (ColorSlice S first)) (ps : FiniteLaw (ColorSlice S second))
    (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1) (w : RetainedLeaf S first second) :
    (law S first second pf ps a ha ha').mass w =
      (colorMix S first second pf ps a ha ha').mass w.val := rfl

theorem law_map_mass {U : Type*} [Fintype U]
    (S : FlaggedTensor X Y Z) (first second : Color)
    (pf : FiniteLaw (ColorSlice S first)) (ps : FiniteLaw (ColorSlice S second))
    (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1) (f : Leaf S → U) (u : U) :
    ((law S first second pf ps a ha ha').map (fun w => f w.val)).mass u =
      ((colorMix S first second pf ps a ha ha').map f).mass u := by
  rw [FiniteLaw.map_mass]
  simp only [law_mass]
  rw [retained_sum S first second
    (fun w => if f w = u then (colorMix S first second pf ps a ha ha').mass w else 0)]
  rw [sum_subtype_indicator (fun w : Leaf S =>
    leafColor S w = first ∨ leafColor S w = second)
    (fun w => if f w = u then (colorMix S first second pf ps a ha ha').mass w else 0)]
  rw [FiniteLaw.map_mass]
  apply Finset.sum_congr rfl
  intro w _
  by_cases h : leafColor S w = first ∨ leafColor S w = second
  · simp [h]
  · have hz := colorMix_mass_zero S first second pf ps a ha ha' w
      (fun h' => h (Or.inl h')) (fun h' => h (Or.inr h'))
    simp [h, hz]

theorem law_entropy (S : FlaggedTensor X Y Z) (first second : Color)
    (hne : first ≠ second)
    (pf : FiniteLaw (ColorSlice S first)) (ps : FiniteLaw (ColorSlice S second))
    (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1) :
    finiteEntropy (law S first second pf ps a ha ha').mass =
      entropyTerm a + entropyTerm (1 - a) +
        a * finiteEntropy pf.mass + (1 - a) * finiteEntropy ps.mass := by
  have hmap : ((law S first second pf ps a ha ha').map Subtype.val).mass =
      (colorMix S first second pf ps a ha ha').mass := by
    funext w
    exact (law_map_mass S first second pf ps a ha ha' id w).trans
      ((colorMix S first second pf ps a ha ha').map_mass_apply id Function.injective_id w)
  rw [← (law S first second pf ps a ha ha').map_entropy_of_injective
    Subtype.val Subtype.val_injective, hmap]
  exact colorMix_entropy S first second hne pf ps a ha ha'

end MatrixMultiplication.CompletionTerminationLaw

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_EntropyHelpers
attribute [-simp] _root_.OAI.MatrixMultiplication.CompletionProductLaws.independentProduct_mass _root_.OAI.MatrixMultiplication.CompletionProductLaws.sigmaJoint_mass _root_.OAI.MatrixMultiplication.ConditionalLabels.normalizedCountLaw_mass _root_.OAI.MatrixMultiplication.Foundation.RationalLaw.toFiniteLaw_mass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualEntropyHelpers

open MatrixMultiplication.Foundation
open scoped BigOperators

variable {A B C X : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype X]

theorem map_comp_mass (p : FiniteLaw A) (f : A → B) (g : B → C) :
    ((p.map f).map g).mass = (p.map (fun a => g (f a))).mass := by
  classical
  funext c
  simp only [FiniteLaw.map_mass]
  calc
    (∑ b, if g b = c then ∑ a, if f a = b then p.mass a else 0 else 0) =
        ∑ b, ∑ a, if f a = b then (if g b = c then p.mass a else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases h : g b = c <;> simp [h]
    _ = ∑ a, ∑ b, if f a = b then (if g b = c then p.mass a else 0) else 0 :=
      Finset.sum_comm
    _ = ∑ a, if g (f a) = c then p.mass a else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      simp

theorem pair_entropy (p : FiniteLaw A) (f : A → B) (g : A → C) :
    finiteEntropy (p.map (fun a => (f a, g a))).mass =
      finiteEntropy (p.map f).mass +
        ∑ b, (p.map f).mass b * finiteEntropy ((p.conditional f b).map g).mass := by
  have hm : ((p.map f).joint (fun b => (p.conditional f b).map g)).mass =
      (p.map (fun a => (f a, g a))).mass := by
    funext bc
    exact p.map_mass_mul_conditional_map f g bc.1 bc.2
  rw [← hm, FiniteLaw.joint_entropy]

theorem conditional_independence_entropy (p : FiniteLaw A)
    (f : A → B) (g : A → C) (x : A → X)
    (independent : ∀ b, 0 < (p.map f).mass b → ∀ c xx,
      ((p.conditional f b).map (fun a => (g a, x a))).mass (c, xx) =
        ((p.conditional f b).map g).mass c *
          ((p.conditional f b).map x).mass xx) :
    finiteEntropy (p.map (fun a => ((f a, g a), x a))).mass -
        finiteEntropy (p.map (fun a => (f a, g a))).mass =
      finiteEntropy (p.map (fun a => (f a, x a))).mass -
        finiteEntropy (p.map f).mass := by
  classical
  have hassoc : finiteEntropy (p.map (fun a => ((f a, g a), x a))).mass =
      finiteEntropy (p.map (fun a => (f a, (g a, x a)))).mass := by
    have h := (p.map (fun a => ((f a, g a), x a))).map_entropy_of_injective
      (Equiv.prodAssoc B C X) (Equiv.prodAssoc B C X).injective
    rw [map_comp_mass] at h
    exact h.symm
  have hcond (b : B) :
      (p.map f).mass b *
          finiteEntropy ((p.conditional f b).map (fun a => (g a, x a))).mass =
        (p.map f).mass b *
          (finiteEntropy ((p.conditional f b).map g).mass +
            finiteEntropy ((p.conditional f b).map x).mass) := by
    by_cases hb : (p.map f).mass b = 0
    · simp only [hb, zero_mul]
    · have hpos : 0 < (p.map f).mass b :=
        lt_of_le_of_ne ((p.map f).nonneg b) (Ne.symm hb)
      have hm : ((p.conditional f b).map (fun a => (g a, x a))).mass =
          (((p.conditional f b).map g).joint
            (fun _ => (p.conditional f b).map x)).mass := by
        funext cx
        exact independent b hpos cx.1 cx.2
      rw [hm, CompletionLaws.independent_entropy]
  rw [hassoc, pair_entropy p f (fun a => (g a, x a)),
    pair_entropy p f g, pair_entropy p f x]
  simp_rw [hcond]
  simp only [mul_add, Finset.sum_add_distrib]
  ring

end MatrixMultiplication.DualEntropyHelpers

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_Information
attribute [-instance] _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.labelRecordZero_subsingleton
attribute [-simp] _root_.OAI.MatrixMultiplication.CW75ReorderedExecution.pairingProduct_zero _root_.OAI.MatrixMultiplication.CompletionExecution.pairingProduct_zero _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_auxiliaryRank _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_columns _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_inner _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_multiplicity _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_occurrences _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_rows _root_.OAI.MatrixMultiplication.CompletionProductLaws.independentProduct_mass _root_.OAI.MatrixMultiplication.CompletionProductLaws.sigmaJoint_mass _root_.OAI.MatrixMultiplication.ConditionalLabels.normalizedCountLaw_mass _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_inner _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_multiplicity _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_outer _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_rank _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.appendCode_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.appendPrefix_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.decodedFine_eq_geometryDecode _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.encodeSourceWord_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.finePrefix_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.mem_conditionalFinset _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.oldPrefix_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.rootPrefixWord_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourcePrefixEquiv_apply_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourcePrefixEquiv_symm_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourceSymbol_encodeSourceWord _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourceSymbol_record
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualInformation

open MatrixMultiplication.Foundation DualEntropyHelpers
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

universe u v w

variable {A : Type u} [Fintype A] {X : Type w} [Fintype X]

theorem conditionalIndependent_of_mass_factorization {R L : Type*}
    [Fintype R] [Fintype L] (p : FiniteLaw A)
    (prior : A → R) (label : A → L) (x : A → X)
    (factor : ConditionalMassFactorization p prior label x) :
    ConditionalIndependent p prior label x := by
  intro r hr l xx
  have h := factor r l xx
  rw [← p.map_mass_mul_conditional_map prior (fun a => (label a, x a)) r (l, xx),
    ← p.map_mass_mul_conditional_map prior label r l,
    ← p.map_mass_mul_conditional_map prior x r xx] at h
  apply mul_left_cancel₀ (mul_ne_zero hr.ne' hr.ne')
  calc
    ((p.map prior).mass r * (p.map prior).mass r) *
        ((p.conditional prior r).map (fun a => (label a, x a))).mass (l, xx) =
        ((p.map prior).mass r *
          ((p.conditional prior r).map (fun a => (label a, x a))).mass (l, xx)) *
            (p.map prior).mass r := by ring
    _ = ((p.map prior).mass r * ((p.conditional prior r).map label).mass l) *
        ((p.map prior).mass r * ((p.conditional prior r).map x).mass xx) := h
    _ = ((p.map prior).mass r * (p.map prior).mass r) *
        (((p.conditional prior r).map label).mass l *
          ((p.conditional prior r).map x).mass xx) := by ring

theorem joint_append_readable_entropy {R L : Type*} [Fintype R] [Fintype L]
    (p : FiniteLaw A) (prior : A → R) (label : A → L) (x : A → X)
    (read : R × X → L) (hread : ∀ a, read (prior a, x a) = label a) :
    finiteEntropy (p.map (fun a => ((prior a, label a), x a))).mass =
      finiteEntropy (p.map (fun a => (prior a, x a))).mass := by
  let lift : R × X → (R × L) × X := fun rx => ((rx.1, read rx), rx.2)
  have hinj : Function.Injective lift := by
    intro a b h
    apply Prod.ext
    · exact congrArg (fun t : (R × L) × X => t.1.1) h
    · exact congrArg (fun t : (R × L) × X => t.2) h
  have hcomp : (fun a => lift (prior a, x a)) =
      (fun a => ((prior a, label a), x a)) := by
    funext a
    simp only [lift, hread]
  have hm := map_comp_mass p (fun a => (prior a, x a)) lift
  rw [hcomp] at hm
  calc
    finiteEntropy (p.map (fun a => ((prior a, label a), x a))).mass =
        finiteEntropy (((p.map (fun a => (prior a, x a))).map lift).mass) := by
      rw [hm]
    _ = _ := (p.map (fun a => (prior a, x a))).map_entropy_of_injective lift hinj

variable {Label : ℕ → Type v} [∀ n, Fintype (Label n)]

@[simp] theorem remainingEntropy_zero (p : FiniteLaw A)
    (labels : ∀ n, A → Label n) (x : A → X) :
    remainingEntropy p labels x 0 = finiteEntropy (p.map x).mass := by
  have hm := map_comp_mass p x (fun xx : X => ((PUnit.unit : PUnit.{v + 1}), xx))
  have he : finiteEntropy (p.map (fun a => (labelRecordOf labels 0 a, x a))).mass =
      finiteEntropy (p.map x).mass := by
    change finiteEntropy (p.map (fun a => ((PUnit.unit : PUnit.{v + 1}), x a))).mass =
      finiteEntropy (p.map x).mass
    rw [← hm]
    exact (p.map x).map_entropy_of_injective _ (fun _ _ h => congrArg Prod.snd h)
  have hz : finiteEntropy (p.map (labelRecordOf labels 0)).mass = 0 := by
    change finiteEntropy (p.map (fun _ : A => (PUnit.unit : PUnit.{v + 1}))).mass = 0
    simp [finiteEntropy, FiniteLaw.map_mass, p.total, entropyTerm]
  rw [remainingEntropy, he, hz, sub_zero]

theorem remainingEntropy_complete (p : FiniteLaw A)
    (labels : ∀ n, A → Label n) (x : A → X) (depth : ℕ)
    (complete : Function.Injective (labelRecordOf labels depth)) :
    remainingEntropy p labels x depth = 0 := by
  have hi : Function.Injective (fun a => (labelRecordOf labels depth a, x a)) :=
    fun _ _ h => complete (congrArg Prod.fst h)
  rw [remainingEntropy, p.map_entropy_of_injective _ hi,
    p.map_entropy_of_injective _ complete, sub_self]

theorem prefix_entropy_succ (p : FiniteLaw A) (labels : ∀ n, A → Label n)
    (depth n : ℕ) (hn : n < depth) :
    finiteEntropy (p.map (labelRecordOf labels (n + 1))).mass =
      finiteEntropy (p.map (labelRecordOf labels n)).mass +
        (FiniteLabelHierarchy.ofLawLabels p labels depth).refinementEntropy n := by
  have h := (FiniteLabelHierarchy.ofLawLabels p labels depth).prefixLaw_entropy_succ
    n (Nat.succ_le_of_lt hn)
  rw [FiniteLabelHierarchy.ofLawLabels_prefixLaw_mass,
    FiniteLabelHierarchy.ofLawLabels_prefixLaw_mass] at h
  exact h

theorem remainingEntropy_succ_readable (p : FiniteLaw A)
    (labels : ∀ n, A → Label n) (x : A → X) (depth n : ℕ) (hn : n < depth)
    (read : LabelRecord Label n × X → Label n)
    (hread : ∀ a, read (labelRecordOf labels n a, x a) = labels n a) :
    remainingEntropy p labels x n - remainingEntropy p labels x (n + 1) =
      (FiniteLabelHierarchy.ofLawLabels p labels depth).refinementEntropy n := by
  have hj := joint_append_readable_entropy p (labelRecordOf labels n) (labels n)
    x read hread
  have hp := prefix_entropy_succ p labels depth n hn
  change finiteEntropy (p.map (fun a => (labelRecordOf labels (n + 1) a, x a))).mass =
    finiteEntropy (p.map (fun a => (labelRecordOf labels n a, x a))).mass at hj
  unfold remainingEntropy
  rw [hj, hp]
  ring

theorem remainingEntropy_succ_independent (p : FiniteLaw A)
    (labels : ∀ n, A → Label n) (x : A → X) (n : ℕ)
    (independent : ConditionalIndependent p (labelRecordOf labels n) (labels n) x) :
    remainingEntropy p labels x (n + 1) = remainingEntropy p labels x n := by
  exact conditional_independence_entropy p (labelRecordOf labels n) (labels n) x independent

theorem incident_rate_eq_coordinate_entropy (p : FiniteLaw A)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (reader : Fin depth → ReaderPair) (x : A → X)
    (complete : Function.Injective (labelRecordOf labels depth))
    (readable : ∀ n : Fin depth, reader n ≠ .yz →
      ∃ read : LabelRecord Label n.val × X → Label n.val,
        ∀ a, read (labelRecordOf labels n.val a, x a) = labels n.val a)
    (independent : ∀ n : Fin depth, reader n = .yz →
      ConditionalIndependent p (labelRecordOf labels n.val) (labels n.val) x) :
    ConditionalLabels.lawPairingRate p labels depth reader .xy +
      ConditionalLabels.lawPairingRate p labels depth reader .xz =
        finiteEntropy (p.map x).mass := by
  let E := remainingEntropy p labels x
  have hterm (n : Fin depth) :
      (if reader n = .xy then
        (FiniteLabelHierarchy.ofLawLabels p labels depth).refinementEntropy n.val else 0) +
      (if reader n = .xz then
        (FiniteLabelHierarchy.ofLawLabels p labels depth).refinementEntropy n.val else 0) =
        E n.val - E (n.val + 1) := by
    by_cases hi : reader n = .yz
    · have he := remainingEntropy_succ_independent p labels x n.val (independent n hi)
      simp only [hi, reduceCtorEq, ite_false, if_false]
      change 0 + 0 = remainingEntropy p labels x n.val -
        remainingEntropy p labels x (n.val + 1)
      rw [he]
      ring
    · obtain ⟨read, hread⟩ := readable n hi
      have he := remainingEntropy_succ_readable p labels x depth n.val n.isLt read hread
      change _ = remainingEntropy p labels x n.val -
        remainingEntropy p labels x (n.val + 1)
      rw [he]
      cases hr : reader n <;> simp_all
  have htel : ∀ k, (∑ n ∈ Finset.range k, (E n - E (n + 1))) = E 0 - E k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih]; ring
  calc
    ConditionalLabels.lawPairingRate p labels depth reader .xy +
        ConditionalLabels.lawPairingRate p labels depth reader .xz =
        ∑ n : Fin depth, (E n.val - E (n.val + 1)) := by
      simp only [ConditionalLabels.lawPairingRate, ConditionalLabels.pairingRate,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun n _ => hterm n)
    _ = E 0 - E depth := by
      calc
        (∑ n : Fin depth, (E n.val - E (n.val + 1))) =
            ∑ n ∈ Finset.range depth, (E n - E (n + 1)) :=
          Fin.sum_univ_eq_sum_range (fun n => E n - E (n + 1)) depth
        _ = E 0 - E depth := htel depth
    _ = finiteEntropy (p.map x).mass := by
      rw [show E 0 = finiteEntropy (p.map x).mass from remainingEntropy_zero p labels x,
        show E depth = 0 from remainingEntropy_complete p labels x depth complete, sub_zero]

end MatrixMultiplication.DualInformation

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_InformationConditioning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualInformation

open MatrixMultiplication.Foundation CompletionLaws
attribute [local instance] Classical.propDecidable Classical.decEq

variable {A R L X : Type*} [Fintype A] [Fintype R] [Fintype L] [Fintype X]

theorem conditionalMassFactorization_condition (p : FiniteLaw A)
    (prior : A → R) (label : A → L) (x : A → X) (Q : R → Prop)
    (h : 0 < eventMass p (fun a => Q (prior a)))
    (factor : ConditionalMassFactorization p prior label x) :
    ConditionalMassFactorization (condition p (fun a => Q (prior a)) h)
      (fun a => prior a.val) (fun a => label a.val) (fun a => x a.val) := by
  intro r l xx
  have hj := condition_coordinate_mass p (fun a => (prior a, (label a, x a)))
    (fun v => Q v.1) h (r, (l, xx))
  have hr := condition_coordinate_mass p prior Q h r
  have hl := condition_coordinate_mass p (fun a => (prior a, label a))
    (fun v => Q v.1) h (r, l)
  have hx := condition_coordinate_mass p (fun a => (prior a, x a))
    (fun v => Q v.1) h (r, xx)
  change
    ((condition p (fun a => Q (prior a)) h).map
      (fun a => (prior a.val, (label a.val, x a.val)))).mass (r, (l, xx)) *
        ((condition p (fun a => Q (prior a)) h).map (fun a => prior a.val)).mass r =
      ((condition p (fun a => Q (prior a)) h).map
        (fun a => (prior a.val, label a.val))).mass (r, l) *
          ((condition p (fun a => Q (prior a)) h).map
            (fun a => (prior a.val, x a.val))).mass (r, xx)
  rw [hj, hr, hl, hx]
  by_cases hQ : Q r
  · simp only [hQ, ite_true, if_true]
    rw [div_mul_div_comm, div_mul_div_comm, factor r l xx]
  · simp only [hQ, ite_false, if_false, zero_mul]

end MatrixMultiplication.DualInformation

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_InformationTransport
attribute [-simp] _root_.OAI.MatrixMultiplication.CompletionProductLaws.independentProduct_mass _root_.OAI.MatrixMultiplication.CompletionProductLaws.sigmaJoint_mass _root_.OAI.MatrixMultiplication.ConditionalLabels.normalizedCountLaw_mass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualInformationTransport

open MatrixMultiplication.Foundation DualEntropyHelpers DualInformation
open scoped BigOperators

variable {A B R L X R' L' X' : Type*}
  [Fintype A] [Fintype B] [Fintype R] [Fintype L] [Fintype X]
  [Fintype R'] [Fintype L'] [Fintype X']

theorem mass_factorization_congr_mass_iff (p q : FiniteLaw A)
    (hmass : p.mass = q.mass) (prior : A → R) (label : A → L) (x : A → X) :
    ConditionalMassFactorization p prior label x ↔
      ConditionalMassFactorization q prior label x := by
  classical
  simp only [ConditionalMassFactorization, FiniteLaw.map_mass, hmass]

theorem mass_factorization_map_iff (p : FiniteLaw A) (e : A → B)
    (prior : B → R) (label : B → L) (x : B → X) :
    ConditionalMassFactorization (p.map e) prior label x ↔
      ConditionalMassFactorization p (fun a => prior (e a))
        (fun a => label (e a)) (fun a => x (e a)) := by
  simp only [ConditionalMassFactorization, map_comp_mass]

theorem map_mass_eq_of_fiber (p : FiniteLaw A) (f : A → B) (g : A → R)
    (b : B) (r : R) (fiber : ∀ a, f a = b ↔ g a = r) :
    (p.map f).mass b = (p.map g).mass r := by
  classical
  simp only [FiniteLaw.map_mass]
  apply Finset.sum_congr rfl
  intro a _
  rw [fiber a]

theorem mass_factorization_of_same_partitions (p : FiniteLaw A)
    (priorA : A → R) (labelA : A → L) (xA : A → X)
    (priorB : A → R') (labelB : A → L') (xB : A → X')
    (hprior : ∀ a b, priorA a = priorA b ↔ priorB a = priorB b)
    (hlabel : ∀ a b, labelA a = labelA b ↔ labelB a = labelB b)
    (hx : ∀ a b, xA a = xA b ↔ xB a = xB b)
    (factor : ConditionalMassFactorization p priorA labelA xA) :
    ConditionalMassFactorization p priorB labelB xB := by
  classical
  intro r l xx
  by_cases hr : ∃ a, priorB a = r
  · obtain ⟨a, rfl⟩ := hr
    by_cases hl : ∃ b, labelB b = l
    · obtain ⟨b, rfl⟩ := hl
      by_cases hxx : ∃ c, xB c = xx
      · obtain ⟨c, rfl⟩ := hxx
        have hp : (p.map priorB).mass (priorB a) =
            (p.map priorA).mass (priorA a) :=
          map_mass_eq_of_fiber p priorB priorA _ _ (fun d => (hprior d a).symm)
        have hpl : (p.map (fun d => (priorB d, labelB d))).mass
              (priorB a, labelB b) =
            (p.map (fun d => (priorA d, labelA d))).mass (priorA a, labelA b) := by
          apply map_mass_eq_of_fiber
          intro d
          simp only [Prod.mk.injEq, ← hprior, ← hlabel]
        have hpx : (p.map (fun d => (priorB d, xB d))).mass
              (priorB a, xB c) =
            (p.map (fun d => (priorA d, xA d))).mass (priorA a, xA c) := by
          apply map_mass_eq_of_fiber
          intro d
          simp only [Prod.mk.injEq, ← hprior, ← hx]
        have hplx : (p.map (fun d => (priorB d, (labelB d, xB d)))).mass
              (priorB a, (labelB b, xB c)) =
            (p.map (fun d => (priorA d, (labelA d, xA d)))).mass
              (priorA a, (labelA b, xA c)) := by
          apply map_mass_eq_of_fiber
          intro d
          simp only [Prod.mk.injEq, ← hprior, ← hlabel, ← hx]
        rw [hplx, hp, hpl, hpx]
        exact factor (priorA a) (labelA b) (xA c)
      · have hn : ∀ c, xB c ≠ xx := not_exists.mp hxx
        simp [FiniteLaw.map_mass, Prod.mk.injEq, hn]
    · have hn : ∀ b, labelB b ≠ l := not_exists.mp hl
      simp [FiniteLaw.map_mass, Prod.mk.injEq, hn]
  · have hn : ∀ a, priorB a ≠ r := not_exists.mp hr
    simp [FiniteLaw.map_mass, Prod.mk.injEq, hn]

end MatrixMultiplication.DualInformationTransport

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_UniformProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualUniformProducts

open MatrixMultiplication.Foundation CompletionProductLaws CompletionLaws
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A X Y : I → Type*}
variable [∀ i, Fintype (A i)] [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]

theorem supportWord_card (P : ∀ i, X i → Prop) :
    Fintype.card {x : ∀ i, X i // ∀ i, P i (x i)} =
      ∏ i, Fintype.card {x : X i // P i x} := by
  rw [Fintype.card_congr (supportWordEquiv P), Fintype.card_pi]

theorem independentProduct_uniformCoordinate
    (p : ∀ i, FiniteLaw (A i)) (f : ∀ i, A i → X i)
    (P : ∀ i, X i → Prop)
    (h : ∀ i, UniformCoordinate (p i) (f i) (P i)) :
    UniformCoordinate (independentProduct p) (fun a i => f i (a i))
      (fun x => ∀ i, P i (x i)) := by
  have hmass (i : I) (x : X i) :
      ((p i).map (f i)).mass x =
        if P i x then (Fintype.card {x : X i // P i x} : ℝ)⁻¹ else 0 := h i x
  intro x
  rw [independentProduct_map_mass]
  simp_rw [hmass]
  by_cases hx : ∀ i, P i (x i)
  · rw [ite_eq_left hx]
    simp only [hx, ite_true, if_true]
    rw [supportWord_card]
    simp only [Nat.cast_prod, Finset.prod_inv_distrib]
  · rw [ite_eq_right hx]
    obtain ⟨i, hi⟩ := not_forall.mp hx
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

theorem independentProduct_joint_mass
    (p : ∀ i, FiniteLaw (A i))
    (f : ∀ i, A i → X i) (g : ∀ i, A i → Y i)
    (x : ∀ i, X i) (y : ∀ i, Y i) :
    ((independentProduct p).map
      (fun a => ((fun i => f i (a i)), (fun i => g i (a i))))).mass (x, y) =
      ∏ i, ((p i).map (fun a => (f i a, g i a))).mass (x i, y i) := by
  calc
    _ = ((independentProduct p).map
        (fun a i => (f i (a i), g i (a i)))).mass (fun i => (x i, y i)) := by
      simp only [FiniteLaw.map_mass, Prod.mk.injEq, funext_iff, forall_and]
    _ = _ := independentProduct_map_mass p (fun i a => (f i a, g i a)) _

theorem independentProduct_independent
    (p : ∀ i, FiniteLaw (A i))
    (f : ∀ i, A i → X i) (g : ∀ i, A i → Y i)
    (h : ∀ i x y, ((p i).map (fun a => (f i a, g i a))).mass (x, y) =
      ((p i).map (f i)).mass x * ((p i).map (g i)).mass y)
    (x : ∀ i, X i) (y : ∀ i, Y i) :
    ((independentProduct p).map
      (fun a => ((fun i => f i (a i)), (fun i => g i (a i))))).mass (x, y) =
      ((independentProduct p).map (fun a i => f i (a i))).mass x *
        ((independentProduct p).map (fun a i => g i (a i))).mass y := by
  rw [independentProduct_joint_mass, independentProduct_map_mass,
    independentProduct_map_mass]
  simp_rw [h]
  exact Finset.prod_mul_distrib

end MatrixMultiplication.DualUniformProducts

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_ProgramIndependence
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualProgramIndependence

universe u v w z

open MatrixMultiplication.Foundation DualInformation CompletionProductLaws
open CompletionColorLaws CompletionLabels RecursiveCompletion DualEntropyHelpers
open DualUniformProducts
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

variable {I : Type*} [Fintype I] [DecidableEq I]
  {A : I → Type u} {R : I → Type v} {L : I → Type w} {X : I → Type z}
  [∀ i, Fintype (A i)] [∀ i, Fintype (R i)]
  [∀ i, Fintype (L i)] [∀ i, Fintype (X i)]

theorem independentProduct_triple_mass
    (p : ∀ i, FiniteLaw (A i)) (prior : ∀ i, A i → R i)
    (label : ∀ i, A i → L i) (x : ∀ i, A i → X i)
    (r : ∀ i, R i) (l : ∀ i, L i) (xx : ∀ i, X i) :
    ((independentProduct p).map (fun a => ((fun i => prior i (a i)),
      ((fun i => label i (a i)), (fun i => x i (a i)))))).mass (r, (l, xx)) =
      ∏ i, ((p i).map (fun a => (prior i a, (label i a, x i a)))).mass
        (r i, (l i, xx i)) := by
  rw [← independentProduct_map_mass p
    (fun i a => (prior i a, (label i a, x i a)))
    (fun i => (r i, (l i, xx i)))]
  simp only [FiniteLaw.map_mass]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Prod.mk.injEq, funext_iff, forall_and]

theorem independentProduct_factorization
    (p : ∀ i, FiniteLaw (A i)) (prior : ∀ i, A i → R i)
    (label : ∀ i, A i → L i) (x : ∀ i, A i → X i)
    (h : ∀ i, ConditionalMassFactorization (p i) (prior i) (label i) (x i)) :
    ConditionalMassFactorization (independentProduct p)
      (fun a i => prior i (a i)) (fun a i => label i (a i))
      (fun a i => x i (a i)) := by
  intro r l xx
  rw [independentProduct_triple_mass p prior label x r l xx,
    independentProduct_map_mass p prior r,
    independentProduct_joint_mass p prior label r l,
    independentProduct_joint_mass p prior x r xx,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact h i (r i) (l i) (xx i)

section Constant

variable {B : Type u} {P : Type v} {C : Type w} {Y : Type z}
  [Fintype B] [Fintype P] [Fintype C] [Fintype Y]

theorem factorization_constant_label (p : FiniteLaw B) (prior : B → P)
    (c : C) (x : B → Y) :
    ConditionalMassFactorization p prior (fun _ => c) x := by
  intro r l xx
  by_cases h : c = l
  · subst l
    simp only [FiniteLaw.map_mass, Prod.mk.injEq, true_and, and_true]
    ring
  · simp only [FiniteLaw.map_mass, Prod.mk.injEq, h, false_and, and_false,
      ite_false, if_false, Finset.sum_const_zero, zero_mul]

end Constant

section ColorMixture

variable {SX SY SZ : Type u} {P : Type v} {C : Type w} {V : Type z}
  [Fintype SX] [Fintype SY] [Fintype SZ]
  [Fintype P] [Fintype C] [Fintype V]

theorem colorSlice_context_mass (S : FlaggedTensor SX SY SZ) (color c : Color)
    (p : FiniteLaw (ColorSlice S color)) (f : Leaf S → V) (v : V) :
    ((p.map Subtype.val).map (fun a => (leafColor S a, f a))).mass (c, v) =
      if color = c then (p.map (fun a => f a.val)).mass v else 0 := by
  rw [map_comp_mass]
  simp only [FiniteLaw.map_mass, Prod.mk.injEq]
  by_cases h : color = c
  · simp only [show ∀ a : ColorSlice S color, leafColor S a.val = color from
      fun a => a.property, h, true_and, ite_true, if_true]
  · simp only [show ∀ a : ColorSlice S color, leafColor S a.val = color from
      fun a => a.property, h, false_and, ite_false, if_false, Finset.sum_const_zero]

theorem colorMix_context_mass (S : FlaggedTensor SX SY SZ) (center output c : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) (f : Leaf S → V) (v : V) :
    ((colorMix S center output pc po α hα hα').map
      (fun a => (leafColor S a, f a))).mass (c, v) =
      α * (if center = c then (pc.map (fun a => f a.val)).mass v else 0) +
        (1 - α) * (if output = c then (po.map (fun a => f a.val)).mass v else 0) := by
  rw [colorMix_map_mass, colorSlice_context_mass, colorSlice_context_mass]

theorem colorMix_refined_context_mass (S : FlaggedTensor SX SY SZ)
    (center output c : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1)
    (prior : Leaf S → P) (f : Leaf S → V) (r : P) (v : V) :
    ((colorMix S center output pc po α hα hα').map
      (fun a => ((leafColor S a, prior a), f a))).mass ((c, r), v) =
      α * (if center = c then
        (pc.map (fun a => (prior a.val, f a.val))).mass (r, v) else 0) +
        (1 - α) * (if output = c then
          (po.map (fun a => (prior a.val, f a.val))).mass (r, v) else 0) := by
  rw [← colorMix_context_mass S center output c pc po α hα hα'
    (fun a => (prior a, f a)) (r, v)]
  simp only [FiniteLaw.map_mass, Prod.mk.injEq, and_assoc]

theorem colorMix_factorization (S : FlaggedTensor SX SY SZ) (center output : Color)
    (hne : center ≠ output)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1)
    (prior : Leaf S → P) (label : Leaf S → C) (x : Leaf S → V)
    (hc : ConditionalMassFactorization pc (fun a => prior a.val)
      (fun a => label a.val) (fun a => x a.val))
    (ho : ConditionalMassFactorization po (fun a => prior a.val)
      (fun a => label a.val) (fun a => x a.val)) :
    ConditionalMassFactorization (colorMix S center output pc po α hα hα')
      (fun a => (leafColor S a, prior a)) label x := by
  rintro ⟨c, r⟩ l xx
  rw [colorMix_refined_context_mass, colorMix_context_mass,
    colorMix_refined_context_mass, colorMix_refined_context_mass]
  by_cases hcc : center = c
  · subst c
    have hoc : output ≠ center := Ne.symm hne
    simp only [ite_true, if_true, ite_eq_right hoc, mul_zero, add_zero]
    calc
      _ = α ^ 2 *
          ((pc.map (fun a => (prior a.val, (label a.val, x a.val)))).mass (r, (l, xx)) *
            (pc.map (fun a => prior a.val)).mass r) := by ring
      _ = _ := by rw [hc r l xx]; ring
  · by_cases hoc : output = c
    · subst c
      simp only [ite_eq_right hne, ite_true, if_true, mul_zero, zero_add]
      calc
        _ = (1 - α) ^ 2 *
            ((po.map (fun a => (prior a.val, (label a.val, x a.val)))).mass (r, (l, xx)) *
              (po.map (fun a => prior a.val)).mass r) := by ring
        _ = _ := by rw [ho r l xx]; ring
    · simp only [ite_eq_right hcc, ite_eq_right hoc, mul_zero, zero_add]

theorem colorMix_recorded_factorization (S : FlaggedTensor SX SY SZ)
    (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) (hbranch : center ≠ output ∨ α = 0)
    (prior : Leaf S → P) (label : Leaf S → C) (x : Leaf S → V)
    (hc : ConditionalMassFactorization pc (fun a => prior a.val)
      (fun a => label a.val) (fun a => x a.val))
    (ho : ConditionalMassFactorization po (fun a => prior a.val)
      (fun a => label a.val) (fun a => x a.val)) :
    ConditionalMassFactorization (colorMix S center output pc po α hα hα')
      (fun a => (leafColor S a, prior a)) label x := by
  rcases hbranch with hne | hz
  · exact colorMix_factorization S center output hne pc po α hα hα' prior label x hc ho
  · subst α
    rintro ⟨c, r⟩ l xx
    rw [colorMix_refined_context_mass, colorMix_context_mass,
      colorMix_refined_context_mass, colorMix_refined_context_mass]
    by_cases hoc : output = c
    · simp only [zero_mul, zero_add, sub_zero, one_mul, ite_eq_left hoc]
      exact ho r l xx
    · simp only [zero_mul, zero_add, sub_zero, one_mul, ite_eq_right hoc]

end ColorMixture

end MatrixMultiplication.DualProgramIndependence

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_CompletionIndependence
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.labelRecordZero_subsingleton
attribute [-simp] _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_auxiliaryRank _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_columns _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_inner _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_multiplicity _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_occurrences _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_rows _root_.OAI.MatrixMultiplication.CompletionTermination.retainedLeafEquiv_coordinates _root_.OAI.MatrixMultiplication.ConditionalLabels.normalizedCountLaw_mass _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_inner _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_multiplicity _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_outer _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_rank _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_x _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_y _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_z _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.appendCode_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.appendPrefix_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.decodedFine_eq_geometryDecode _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.encodeSourceWord_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.finePrefix_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.mem_conditionalFinset _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.oldPrefix_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.rootPrefixWord_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourcePrefixEquiv_apply_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourcePrefixEquiv_symm_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourceSymbol_encodeSourceWord _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourceSymbol_record
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualProgramIndependence

universe u w

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels
open CompletionLaws CompletionColorLaws CompletionProductLaws
open DualInformation DualInformationTransport TopologicalFlatten
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

variable {X Y Z : Type u} {Code : Type w} [Fintype X] [Fintype Y] [Fintype Z]
  [Fintype Code] [Inhabited Code] {depth m : ℕ}

omit [Fintype X] [Fintype Y] [Fintype Z] [Fintype Code] [Inhabited Code] in
theorem slotPrior_word_eq_iff (S : FlaggedTensor X Y Z)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (i : Fin m) (k : ℕ) (a b : Fin m → Leaf S) :
    (fun j => slotPrior S p i k j (a j)) = (fun j => slotPrior S p i k j (b j)) ↔
      (∀ j, leafColor S (a j) = leafColor S (b j)) ∧
        ((∀ j : Fin m, j.val < i.val →
          labelRecordOf p.labels depth (a j) = labelRecordOf p.labels depth (b j)) ∧
          labelRecordOf p.labels k (a i) = labelRecordOf p.labels k (b i)) := by
  constructor
  · intro h
    refine ⟨fun j => congrArg Prod.fst (congrFun h j), ?_, ?_⟩
    · intro j hj
      have hs := congrArg Prod.snd (congrFun h j)
      change labelRecordOf p.labels (slotCut depth k i j) (a j) =
        labelRecordOf p.labels (slotCut depth k i j) (b j) at hs
      rw [labelRecordOf_eq_iff] at hs ⊢
      simpa only [slotCut, ite_eq_left hj] using hs
    · have hs := congrArg Prod.snd (congrFun h i)
      change labelRecordOf p.labels (slotCut depth k i i) (a i) =
        labelRecordOf p.labels (slotCut depth k i i) (b i) at hs
      rw [labelRecordOf_eq_iff] at hs ⊢
      simpa [slotCut] using hs
  · rintro ⟨hc, hp, hi⟩
    funext j
    apply Prod.ext (hc j)
    change labelRecordOf p.labels (slotCut depth k i j) (a j) =
      labelRecordOf p.labels (slotCut depth k i j) (b j)
    rw [labelRecordOf_eq_iff]
    intro n hn
    by_cases hj : j.val < i.val
    · have hn' : n < depth := by simpa only [slotCut, ite_eq_left hj] using hn
      exact label_eq_of_record_eq p.labels (hp j hj) hn'
    · by_cases hji : j = i
      · subst j
        have hn' : n < k := by simpa [slotCut] using hn
        exact label_eq_of_record_eq p.labels hi hn'
      · simp only [slotCut, ite_eq_right hj, ite_eq_right hji] at hn
        exact (Nat.not_lt_zero n hn).elim

omit [Fintype X] [Fintype Y] [Fintype Z] [Fintype Code] in
theorem slotLabel_word_eq_iff (S : FlaggedTensor X Y Z)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (i : Fin m) (k : ℕ) (a b : Fin m → Leaf S) :
    (fun j => slotLabel S p i k j (a j)) = (fun j => slotLabel S p i k j (b j)) ↔
      p.labels k (a i) = p.labels k (b i) := by
  constructor
  · intro h
    simpa only [slotLabel, ite_eq_left rfl, ite_true, if_true] using congrFun h i
  · intro h
    funext j
    by_cases hji : j = i
    · subst j
      simpa only [slotLabel, ite_eq_left rfl, ite_true, if_true] using h
    · simp only [slotLabel, ite_eq_right hji]

theorem iidColorLaw_slot_factorization (S : FlaggedTensor X Y Z)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) (hbranch : center ≠ output ∨ α = 0)
    (i : Fin m) (k : ℕ)
    (hc : ConditionalMassFactorization pc (fun a => labelRecordOf p.labels k a.val)
      (fun a => p.labels k a.val) (fun a => a.val.val.1))
    (ho : ConditionalMassFactorization po (fun a => labelRecordOf p.labels k a.val)
      (fun a => p.labels k a.val) (fun a => a.val.val.1)) :
    ConditionalMassFactorization (iidColorLaw S center output pc po m α hα hα')
      (fun a j => slotPrior S p i k j (a j))
      (fun a j => slotLabel S p i k j (a j)) (fun a j => (a j).val.1) := by
  apply independentProduct_factorization
    (fun _ : Fin m => colorMix S center output pc po α hα hα')
    (slotPrior S p i k) (slotLabel S p i k) (fun _ a => a.val.1)
  intro j
  by_cases hji : j = i
  · subst j
    apply mass_factorization_of_same_partitions (colorMix S center output pc po α hα hα')
      (fun a => (leafColor S a, labelRecordOf p.labels k a)) (p.labels k) (fun a => a.val.1)
    · intro a b
      simp only [slotPrior, Prod.mk.injEq, labelRecordOf_eq_iff]
      simp [slotCut]
    · intro a b
      simp [slotLabel]
    · intro a b
      rfl
    · exact colorMix_recorded_factorization S center output pc po α hα hα' hbranch
        (labelRecordOf p.labels k) (p.labels k) (fun a => a.val.1) hc ho
  · have hl : slotLabel S p i k j = (fun _ => (default : Code)) := by
      funext a
      simp [slotLabel, hji]
    rw [hl]
    exact factorization_constant_label (colorMix S center output pc po α hα hα')
      (slotPrior S p i k j) (default : Code) (fun a => a.val.1)

theorem condition_slot_factorization (S : FlaggedTensor X Y Z)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α < 1) (hbranch : center ≠ output ∨ α = 0)
    (hm : 0 < m) (i : Fin m) (k : ℕ)
    (hc : ConditionalMassFactorization pc (fun a => labelRecordOf p.labels k a.val)
      (fun a => p.labels k a.val) (fun a => a.val.val.1))
    (ho : ConditionalMassFactorization po (fun a => labelRecordOf p.labels k a.val)
      (fun a => p.labels k a.val) (fun a => a.val.val.1)) :
    ConditionalMassFactorization
      (condition (iidColorLaw S center output pc po m α hα hα'.le)
        (completionEvent S center output m)
        (completionEvent_mass_pos S center output pc po m hm α hα hα'))
      (fun a j => slotPrior S p i k j (a.val j))
      (fun a j => slotLabel S p i k j (a.val j)) (fun a j => (a.val j).val.1) := by
  exact conditionalMassFactorization_condition
    (iidColorLaw S center output pc po m α hα hα'.le)
    (fun a j => slotPrior S p i k j (a j))
    (fun a j => slotLabel S p i k j (a j)) (fun a j => (a j).val.1)
    (slotCompletionEvent center output i k)
    (completionEvent_mass_pos S center output pc po m hm α hα hα')
    (iidColorLaw_slot_factorization S p center output pc po α hα hα'.le hbranch i k hc ho)

theorem conditionalCompletionLaw_inherited_factorization (S : FlaggedTensor X Y Z)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (context_eq : ∀ a, p.context a = leafColor S a)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side)
    (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α < 1) (hbranch : center ≠ output ∨ α = 0)
    (hm : 0 < m) (i : Fin m) (k : ℕ) (hk : k < depth)
    (hc : ConditionalMassFactorization pc (fun a => labelRecordOf p.labels k a.val)
      (fun a => p.labels k a.val) (fun a => a.val.val.1))
    (ho : ConditionalMassFactorization po (fun a => labelRecordOf p.labels k a.val)
      (fun a => p.labels k a.val) (fun a => a.val.val.1)) :
    ConditionalMassFactorization
      (conditionalCompletionLaw S center output pc po m hm α hα hα')
      (fun a => labelRecordOf
        (completionLocalProgram S center m p context_eq view_eq).labels
        (3 + (i.val * depth + k)) a.val)
      (fun a => (completionLocalProgram S center m p context_eq view_eq).labels
        (3 + (i.val * depth + k)) a.val)
      (fun a => a.val.val.1) := by
  let e := conditionalLeafEquiv S center output m
  let q := condition (iidColorLaw S center output pc po m α hα hα'.le)
    (completionEvent S center output m)
    (completionEvent_mass_pos S center output pc po m hm α hα hα')
  have hslot (a : {w : Fin m → Leaf S // completionEvent S center output m w}) :
      slot S center m (e.symm a).val = a.val :=
    congrArg Subtype.val (e.apply_symm_apply a)
  change ConditionalMassFactorization (q.map e.symm) _ _ _
  rw [mass_factorization_map_iff]
  apply mass_factorization_of_same_partitions q
    (fun a j => slotPrior S p i k j (a.val j))
    (fun a j => slotLabel S p i k j (a.val j)) (fun a j => (a.val j).val.1)
  · intro a b
    rw [slotPrior_word_eq_iff, completionProgram_record_eq_iff _ _ _ _ _ _ i k hk.le]
    simp only [(e.symm a).property, (e.symm b).property, true_and, pattern,
      hslot, funext_iff]
  · intro a b
    rw [slotLabel_word_eq_iff,
      completionLocalProgram_label_slot _ _ _ _ _ _ i k hk,
      completionLocalProgram_label_slot _ _ _ _ _ _ i k hk, hslot, hslot]
    simp only [encodeOld, Option.some.injEq, Sum.inr.injEq]
  · intro a b
    rfl
  · exact condition_slot_factorization S p center output pc po α hα hα' hbranch hm i k hc ho

end MatrixMultiplication.DualProgramIndependence

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_WitnessArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualWitness

theorem state_factors : state288.factors = 288 := by
  norm_num [state288, state96, state48, state24, state8, state4, state2,
    initial, minus, plusA, plusC]

end MatrixMultiplication.DualWitness

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Numerical_ComplexRationalLogCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact rational intervals, logarithm bounds and arithmetic circuit soundness. -/

namespace MatrixMultiplication.Foundation.RationalLogCertificate

open scoped BigOperators

theorem symmetric_expansion_error (t : ℝ) (ht : |t| < 1) (n : ℕ) :
    |(Real.log (1 + t) - Real.log (1 - t)) -
        (sumPower t n - sumPower (-t) n)| ≤
      2 * (|t| ^ (n + 1) / (1 - |t|)) := by
  have hminus : |sumPower t n + Real.log (1 - t)| ≤
      |t| ^ (n + 1) / (1 - |t|) :=
    Real.abs_log_sub_add_sum_range_le ht n
  have hplus : |sumPower (-t) n + Real.log (1 + t)| ≤
      |t| ^ (n + 1) / (1 - |t|) := by
    simpa only [sumPower, abs_neg, sub_neg_eq_add] using
      Real.abs_log_sub_add_sum_range_le (by simpa using ht : |-t| < 1) n
  calc
    _ = |(sumPower (-t) n + Real.log (1 + t)) -
        (sumPower t n + Real.log (1 - t))| := by congr 1; ring
    _ ≤ |sumPower (-t) n + Real.log (1 + t)| +
        |sumPower t n + Real.log (1 - t)| := abs_sub _ _
    _ ≤ 2 * (|t| ^ (n + 1) / (1 - |t|)) := by linarith

theorem normalized_variable_bounds (x : ℝ) (hlo : 1 ≤ x) (hhi : x ≤ 2) :
    0 ≤ (x - 1) / (x + 1) ∧ (x - 1) / (x + 1) ≤ 1 / 3 := by
  have hden : 0 < x + 1 := by linarith
  constructor
  · exact div_nonneg (sub_nonneg.mpr hlo) hden.le
  · apply (div_le_iff₀ hden).2
    linarith

theorem normalized_log_error (x : ℝ) (hlo : 1 ≤ x) (hhi : x ≤ 2) (n : ℕ) :
    |Real.log x - realApprox n x| ≤
      2 * (((x - 1) / (x + 1)) ^ (n + 1) / (1 - (x - 1) / (x + 1))) := by
  let t := (x - 1) / (x + 1)
  obtain ⟨ht0, ht3⟩ := normalized_variable_bounds x hlo hhi
  have ht1 : t < 1 := by dsimp [t] <;> linarith
  have hden : x + 1 ≠ 0 := by linarith
  have hminus : 1 - t ≠ 0 := by linarith
  have hplus : 1 + t ≠ 0 := by dsimp [t] <;> linarith
  have hratio : (1 + t) / (1 - t) = x := by
    dsimp [t]
    field_simp [hden]
    ring
  have hlog : Real.log x = Real.log (1 + t) - Real.log (1 - t) := by
    rw [← hratio]
    exact Real.log_div hplus hminus
  have ht0' : 0 ≤ t := ht0
  have herror := symmetric_expansion_error t (by rwa [abs_of_nonneg ht0']) n
  rw [abs_of_nonneg ht0'] at herror
  simpa only [realApprox, ← hlog, t] using herror

theorem normalized_log_error_80 (x : ℝ) (hlo : 1 ≤ x) (hhi : x ≤ 2) :
    |Real.log x - realApprox 80 x| < 1 / (2 : ℝ) ^ 120 := by
  obtain ⟨ht0, ht3⟩ := normalized_variable_bounds x hlo hhi
  apply lt_of_le_of_lt (normalized_log_error x hlo hhi 80)
  calc
    _ ≤ 2 * (((1 : ℝ) / 3) ^ 81 / (1 - 1 / 3)) := by gcongr
    _ < 1 / (2 : ℝ) ^ 120 := by norm_num

theorem rational_log_error_80 (x : ℚ) (hlo : 1 ≤ x) (hhi : x ≤ 2) :
    |Real.log (x : ℝ) - (rationalApprox 80 x : ℝ)| < 1 / (2 : ℝ) ^ 120 := by
  rw [rationalApprox_cast]
  exact normalized_log_error_80 (x : ℝ) (by exact_mod_cast hlo) (by exact_mod_cast hhi)

theorem reduced_log_error {x : ℚ} (d : ReducedArgument x) :
    |Real.log (x : ℝ) - (reducedApprox d : ℝ)| ≤
      (1 + |(d.exponent : ℝ)|) / (2 : ℝ) ^ 120 := by
  have hm : (0 : ℝ) < d.mantissa := by
    have hlo : (1 : ℝ) ≤ d.mantissa := by exact_mod_cast d.lower
    linarith
  have hvalue : (x : ℝ) = (d.mantissa : ℝ) * (2 : ℝ) ^ d.exponent := by
    simpa only [Rat.cast_mul, Rat.cast_zpow, Rat.cast_ofNat] using
      congrArg (fun q : ℚ => (q : ℝ)) d.value
  have hlog : Real.log (x : ℝ) = Real.log (d.mantissa : ℝ) +
      (d.exponent : ℝ) * Real.log 2 := by
    rw [hvalue, Real.log_mul (ne_of_gt hm) (zpow_ne_zero _ (by norm_num)),
      Real.log_zpow]
  have hmerr := (rational_log_error_80 d.mantissa d.lower d.upper).le
  have htwoerr := (rational_log_error_80 2 (by norm_num) (by norm_num)).le
  have hcast : (reducedApprox d : ℝ) = (rationalApprox 80 d.mantissa : ℝ) +
      (d.exponent : ℝ) * (rationalApprox 80 2 : ℝ) := by
    simp [reducedApprox]
  rw [hlog, hcast]
  calc
    _ = |(Real.log (d.mantissa : ℝ) - (rationalApprox 80 d.mantissa : ℝ)) +
        (d.exponent : ℝ) * (Real.log 2 - (rationalApprox 80 2 : ℝ))| := by
      congr 1
      ring
    _ ≤ |Real.log (d.mantissa : ℝ) - (rationalApprox 80 d.mantissa : ℝ)| +
        |(d.exponent : ℝ)| * |Real.log 2 - (rationalApprox 80 2 : ℝ)| := by
      simpa only [abs_mul] using abs_add_le
        (Real.log (d.mantissa : ℝ) - (rationalApprox 80 d.mantissa : ℝ))
        ((d.exponent : ℝ) * (Real.log 2 - (rationalApprox 80 2 : ℝ)))
    _ ≤ 1 / (2 : ℝ) ^ 120 + |(d.exponent : ℝ)| * (1 / (2 : ℝ) ^ 120) := by
      exact add_le_add hmerr (mul_le_mul_of_nonneg_left htwoerr (abs_nonneg _))
    _ = (1 + |(d.exponent : ℝ)|) / (2 : ℝ) ^ 120 := by ring

end MatrixMultiplication.Foundation.RationalLogCertificate

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Numerical_ComplexCertificatesLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact rational intervals, logarithm bounds and arithmetic circuit soundness. -/

namespace MatrixMultiplication.ComplexCertificates

open MatrixMultiplication.Foundation.RationalLogCertificate

theorem log_bounds_of_reduction {x : ℚ} (d : ReducedArgument x) (lo hi : ℚ)
    (hl : lo < reducedApprox d - (1 + |(d.exponent : ℚ)|) / 2 ^ 120)
    (hu : reducedApprox d + (1 + |(d.exponent : ℚ)|) / 2 ^ 120 < hi) :
    (lo : ℝ) < Real.log (x : ℝ) ∧ Real.log (x : ℝ) < (hi : ℝ) := by
  have herror := abs_le.mp (reduced_log_error d)
  have hl' : (lo : ℝ) < (reducedApprox d : ℝ) -
      (1 + |(d.exponent : ℝ)|) / 2 ^ 120 := by exact_mod_cast hl
  have hu' : (reducedApprox d : ℝ) +
      (1 + |(d.exponent : ℝ)|) / 2 ^ 120 < (hi : ℝ) := by exact_mod_cast hu
  constructor <;> linarith

theorem log_two_bounds :
    (34657 : ℝ) / 50000 < Real.log 2 ∧ Real.log 2 < (17329 : ℝ) / 25000 := by
  have h := log_bounds_of_reduction reduceTwo (34657 / 50000) (17329 / 25000)
    (by decide +kernel) (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem log_three_lower : (549 : ℝ) / 500 < Real.log 3 := by
  have h := log_bounds_of_reduction reduceThree (549 / 500) (10987 / 10000)
    (by decide +kernel) (by decide +kernel)
  norm_num at h ⊢
  exact h.1

theorem log_nine_sevenths_bounds :
    (1 : ℝ) / 4 < Real.log (9 / 7 : ℝ) ∧ Real.log (9 / 7 : ℝ) < (63 : ℝ) / 250 := by
  have h := log_bounds_of_reduction reduceNineSevenths (1 / 4) (63 / 250)
    (by decide +kernel) (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem exp_neg_354_lower : (701 : ℝ) / 1000 < Real.exp (-(177 / 500 : ℝ)) := by
  have h := log_bounds_of_reduction reduceExpLo48 (-356 / 1000) (-177 / 500)
    (by decide +kernel) (by decide +kernel)
  have hh : Real.log (701 / 1000 : ℝ) < -(177 / 500 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, neg_div] using h.2
  exact (Real.log_lt_iff_lt_exp (by norm_num)).1 hh

theorem exp_neg_348_upper : Real.exp (-(87 / 250 : ℝ)) < (707 : ℝ) / 1000 := by
  have h := log_bounds_of_reduction reduceExpHi48 (-87 / 250) (-346 / 1000)
    (by decide +kernel) (by decide +kernel)
  have hh : -(87 / 250 : ℝ) < Real.log (707 / 1000 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, neg_div] using h.1
  exact (Real.lt_log_iff_exp_lt (by norm_num)).1 hh

theorem exp_neg_86_lower : (169 : ℝ) / 400 < Real.exp (-(43 / 50 : ℝ)) := by
  have h := log_bounds_of_reduction reduceExpLo288 (-863 / 1000) (-43 / 50)
    (by decide +kernel) (by decide +kernel)
  have hh : Real.log (169 / 400 : ℝ) < -(43 / 50 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, neg_div] using h.2
  exact (Real.log_lt_iff_lt_exp (by norm_num)).1 hh

theorem log_z48_lower :
    (127 : ℝ) / 200 < Real.log ((1 + (701 / 1000 : ℝ)) ^ 2 - 1) := by
  have h := log_bounds_of_reduction reduceZ48Lo (127 / 200) (651 / 1000)
    (by decide +kernel) (by decide +kernel)
  norm_num at h ⊢
  exact h.1

theorem log_z48_upper :
    Real.log ((1 + (707 / 1000 : ℝ)) ^ 2 - 1) < (651 : ℝ) / 1000 := by
  have h := log_bounds_of_reduction reduceZ48Hi (127 / 200) (651 / 1000)
    (by decide +kernel) (by decide +kernel)
  norm_num at h ⊢
  exact h.2

theorem log_z288_lower :
    (157 : ℝ) / 250 < Real.log ((1 + (169 / 400 : ℝ)) ^ 3 - 1) := by
  have h := log_bounds_of_reduction reduceZ288Lo (157 / 250) (16 / 25)
    (by decide +kernel) (by decide +kernel)
  norm_num at h ⊢
  exact h.1

end MatrixMultiplication.ComplexCertificates

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Numerical_ComplexCertificatesDual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact rational intervals, logarithm bounds and arithmetic circuit soundness. -/

namespace MatrixMultiplication.ComplexCertificates

open DualWitness

theorem rho48_bounds : (67 : ℝ) / 125 < rho48 ∧ rho48 < (537 : ℝ) / 1000 := by
  norm_num [rho48, rho24, rho8]

theorem inactive48_lower : (463 : ℝ) / 1000 < 1 - rho48 := by
  norm_num [rho48, rho24, rho8]

theorem inactive288_lower : (9 : ℝ) / 25 < 1 - rho288 := by
  norm_num [rho288, rho96, rho48, rho24, rho8]

theorem delta24_bounds :
    (87 : ℝ) / 250 < delta24 ∧ delta24 < (177 : ℝ) / 500 := by
  obtain ⟨hl, hh⟩ := log_nine_sevenths_bounds
  norm_num [delta24, rho24, rho8]
  constructor <;> linarith

theorem z48_bounds : (127 : ℝ) / 200 < z48 ∧ z48 < (651 : ℝ) / 1000 := by
  obtain ⟨hl, hh⟩ := delta24_bounds
  have helo : (701 : ℝ) / 1000 < Real.exp (-delta24) :=
    exp_neg_354_lower.trans (Real.exp_lt_exp.mpr (by linarith))
  have hehi : Real.exp (-delta24) < (707 : ℝ) / 1000 :=
    (Real.exp_lt_exp.mpr (by linarith : -delta24 < -(87 / 250 : ℝ))).trans
      exp_neg_348_upper
  have harglo : (1 + (701 / 1000 : ℝ)) ^ 2 - 1 <
      (1 + Real.exp (-delta24)) ^ 2 - 1 := by gcongr
  have harghi : (1 + Real.exp (-delta24)) ^ 2 - 1 <
      (1 + (707 / 1000 : ℝ)) ^ 2 - 1 := by gcongr
  have hargpos : 0 < (1 + Real.exp (-delta24)) ^ 2 - 1 := by
    norm_num at harglo
    linarith
  exact ⟨log_z48_lower.trans (Real.log_lt_log (by norm_num) harglo),
    (Real.log_lt_log hargpos harghi).trans log_z48_upper⟩

theorem delta96_bounds : 0 < delta96 ∧ delta96 < (43 : ℝ) / 50 := by
  obtain ⟨hr, hr'⟩ := rho48_bounds
  obtain ⟨hz, hz'⟩ := z48_bounds
  have hd : 0 < 1 + rho48 := by linarith
  constructor
  · exact div_pos (by linarith) hd
  · apply (div_lt_iff₀ hd).2
    linarith

theorem z288_bounds : (157 : ℝ) / 250 < z288 ∧ z288 < 2 := by
  obtain ⟨hd, hd'⟩ := delta96_bounds
  have helo : (169 : ℝ) / 400 < Real.exp (-delta96) :=
    exp_neg_86_lower.trans (Real.exp_lt_exp.mpr (by linarith))
  have hehi : Real.exp (-delta96) < 1 := by
    simpa using Real.exp_lt_exp.mpr (by linarith : -delta96 < 0)
  have harglo : (1 + (169 / 400 : ℝ)) ^ 3 - 1 <
      (1 + Real.exp (-delta96)) ^ 3 - 1 := by gcongr
  have harghi : (1 + Real.exp (-delta96)) ^ 3 - 1 < 7 := by
    have h : (1 + Real.exp (-delta96)) ^ 3 - 1 < (1 + (1 : ℝ)) ^ 3 - 1 := by
      gcongr
    norm_num at h
    exact h
  have hargpos : 0 < (1 + Real.exp (-delta96)) ^ 3 - 1 := by
    norm_num at harglo
    linarith
  have hlog7 : Real.log 7 < 2 := by
    apply (Real.log_lt_iff_lt_exp (by norm_num)).2
    refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) 6)
    norm_num [Finset.sum_range_succ, Nat.factorial]
  exact ⟨log_z288_lower.trans (Real.log_lt_log (by norm_num) harglo),
    (Real.log_lt_log hargpos harghi).trans hlog7⟩

theorem hiddenRate_lower :
    (9 / 64 : ℝ) * (549 / 500) + (463 / 1000 : ℝ) / 48 * (127 / 200) +
      (9 / 25 : ℝ) / 288 * (157 / 250) < hiddenRate := by
  have h3 := log_three_lower
  have h48 := z48_bounds.1
  have h288 := z288_bounds.1
  have hr48 := inactive48_lower
  have hr288 := inactive288_lower
  dsimp [hiddenRate]
  gcongr

theorem dual_aspect_lower : (1548637 : ℝ) / 3327360 < aspect := by
  have h2 := log_two_bounds
  have hD := hiddenRate_lower
  have hl2 : 0 < Real.log 2 := by linarith [h2.1]
  apply (lt_div_iff₀ hl2).2
  norm_num at hD
  linarith [h2.2]

end MatrixMultiplication.ComplexCertificates

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Rectangular_Growth
attribute [-simp] _root_.OAI.MatrixMultiplication.Arithmetic.RecursiveBlock.Family.cost_ofMatrix _root_.OAI.MatrixMultiplication.Arithmetic.naiveAlgorithm_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rectangular matrix multiplication algorithms and their asymptotic exponents. -/

noncomputable section

namespace MatrixMultiplication.Arithmetic

variable {F : Type*} [Field F]

theorem rectangular_power_cost_padding_bound
    {a b : ℕ} (ha : 2 ≤ a) {k s C : ℝ} (hk : 0 ≤ k)
    (hab : (a : ℝ) ^ k ≤ (b : ℝ)) (hs : 0 ≤ s) (hC : 0 < C)
    (hpower : ∀ t : ℕ, ∃ P : MatrixAlgorithm F (a ^ t) (b ^ t) (a ^ t),
      P.Correct ∧ (P.cost : ℝ) ≤ C * ((a : ℝ) ^ s) ^ t) :
    ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ P : MatrixAlgorithm F n (innerSize n k) n,
        P.Correct ∧ (P.cost : ℝ) ≤ D * (n : ℝ) ^ s := by
  have hapos : 0 < (a : ℝ) := by exact_mod_cast (by omega : 0 < a)
  refine ⟨C * (a : ℝ) ^ s, mul_pos hC (Real.rpow_pos_of_pos hapos s), ?_⟩
  intro n hn
  obtain ⟨t, hnt, htn⟩ := MatrixMultiplication.Foundation.Arithmetic.exists_power_cover ha hn
  obtain ⟨P, hP, hcost⟩ := hpower t
  obtain ⟨Q, hQ, hQP⟩ := MatrixAlgorithm.exists_restrict
    hnt (innerSize_le_pow hk hnt hab) hnt P hP
  refine ⟨Q, hQ, ?_⟩
  calc
    (Q.cost : ℝ) ≤ (P.cost : ℝ) := by exact_mod_cast hQP
    _ ≤ C * ((a : ℝ) ^ s) ^ t := hcost
    _ = C * ((a ^ t : ℕ) : ℝ) ^ s := by
      rw [Real.rpow_pow_comm hapos.le, Nat.cast_pow]
    _ ≤ C * ((a : ℝ) * (n : ℝ)) ^ s :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast htn) hs) hC.le
    _ = (C * (a : ℝ) ^ s) * (n : ℝ) ^ s := by
      rw [Real.mul_rpow hapos.le (Nat.cast_nonneg n)]
      ring

theorem rectangularAdmissibleExponent_of_power_costs
    {a b : ℕ} (ha : 2 ≤ a) {k τ : ℝ} (hk : 0 ≤ k)
    (hab : (a : ℝ) ^ k ≤ (b : ℝ)) (hτ : 0 ≤ τ)
    (hpower : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ t : ℕ, ∃ P : MatrixAlgorithm F (a ^ t) (b ^ t) (a ^ t),
        P.Correct ∧ (P.cost : ℝ) ≤ C * ((a : ℝ) ^ (τ + ε)) ^ t) :
    RectangularAdmissibleExponent F k τ := by
  intro ε hε
  obtain ⟨C, hC, hcost⟩ := hpower ε hε
  exact rectangular_power_cost_padding_bound ha hk hab (by linarith) hC hcost

theorem rectangularBlockCost_bound {a b R K : ℕ} (ha : 2 ≤ a)
    {τ ε : ℝ} (hε : 0 < ε)
    (hR : (R : ℝ) ≤ (a : ℝ) ^ τ)
    (hin : (a * b : ℕ) ≤ (a : ℝ) ^ τ)
    (hout : (a : ℝ) ^ (2 : ℕ) ≤ (a : ℝ) ^ τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t,
      (rectangularBlockCost a b R K t : ℝ) ≤ C * ((a : ℝ) ^ (τ + ε)) ^ t := by
  have haone : 1 < (a : ℝ) := by exact_mod_cast (by omega : 1 < a)
  have hrate : (R : ℝ) < (a : ℝ) ^ (τ + ε) :=
    hR.trans_lt (Real.rpow_lt_rpow_of_exponent_lt haone (by linarith))
  have hlarge : (a : ℝ) ^ τ ≤ (a : ℝ) ^ (τ + ε) :=
    Real.rpow_le_rpow_of_exponent_le haone.le (by linarith)
  have hin0 : (0 : ℝ) ≤ (a * b : ℕ) := Nat.cast_nonneg _
  have hd : 0 ≤ max ((a * b : ℕ) : ℝ) ((a : ℝ) ^ (2 : ℕ)) :=
    hin0.trans (le_max_left _ _)
  apply MatrixMultiplication.Foundation.Arithmetic.geometric_cost_recurrence_bound
    (fun t => (rectangularBlockCost a b R K t : ℝ))
    (R : ℝ) (2 * K) (max ((a * b : ℕ) : ℝ) ((a : ℝ) ^ (2 : ℕ)))
    ((a : ℝ) ^ (τ + ε)) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (by positivity) hd hrate (max_le (hin.trans hlarge) (hout.trans hlarge))
  intro t
  simp only [rectangularBlockCost_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
  have h1 : ((a : ℝ) * (b : ℝ)) ^ t ≤
      max ((a * b : ℕ) : ℝ) ((a : ℝ) ^ (2 : ℕ)) ^ t := by
    apply pow_le_pow_left₀ (by positivity)
    simpa only [Nat.cast_mul] using le_max_left ((a * b : ℕ) : ℝ) ((a : ℝ) ^ (2 : ℕ))
  have h2 : ((a : ℝ) ^ (2 : ℕ)) ^ t ≤
      max ((a * b : ℕ) : ℝ) ((a : ℝ) ^ (2 : ℕ)) ^ t :=
    pow_le_pow_left₀ (sq_nonneg _) (le_max_right _ _) t
  simp only [Nat.cast_mul] at h1 h2
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add h1 h2) (Nat.cast_nonneg K)]

theorem rectangular_power_programs_of_block_step {a b R K : ℕ}
    (hscalar : ∃ P : MatrixAlgorithm F 1 1 1, P.Correct ∧ P.cost ≤ 1)
    (hstep : ∀ m p : ℕ, ∀ P : MatrixAlgorithm F m p m, P.Correct →
      ∃ Q : MatrixAlgorithm F (a * m) (b * p) (a * m), Q.Correct ∧
        Q.cost ≤ R * P.cost + K * (m * p + m ^ 2)) :
    ∀ t : ℕ, ∃ P : MatrixAlgorithm F (a ^ t) (b ^ t) (a ^ t),
      P.Correct ∧ P.cost ≤ rectangularBlockCost a b R K t := by
  intro t
  induction t with
  | zero => simpa using hscalar
  | succ t ih =>
    obtain ⟨P, hP, hcost⟩ := ih
    obtain ⟨Q, hQ, hQcost⟩ := hstep (a ^ t) (b ^ t) P hP
    have hbound : Q.cost ≤ rectangularBlockCost a b R K (t + 1) := by
      apply hQcost.trans
      simp only [rectangularBlockCost_succ, mul_pow, ← pow_mul, Nat.mul_comm t 2]
      exact Nat.add_le_add_right (Nat.mul_le_mul_left R hcost) _
    have hresult : ∃ Q : MatrixAlgorithm F (a * a ^ t) (b * b ^ t) (a * a ^ t),
        Q.Correct ∧ Q.cost ≤ rectangularBlockCost a b R K (t + 1) := ⟨Q, hQ, hbound⟩
    exact (pow_succ' a t).symm ▸ ((pow_succ' b t).symm ▸ hresult)

theorem rectangularAdmissibleExponent_of_block_step
    {a b R K : ℕ} (ha : 2 ≤ a) {k τ : ℝ} (hk : 0 ≤ k)
    (hab : (a : ℝ) ^ k ≤ (b : ℝ)) (hτ : 0 ≤ τ)
    (hR : (R : ℝ) ≤ (a : ℝ) ^ τ)
    (hin : (a * b : ℕ) ≤ (a : ℝ) ^ τ)
    (hout : (a : ℝ) ^ (2 : ℕ) ≤ (a : ℝ) ^ τ)
    (hscalar : ∃ P : MatrixAlgorithm F 1 1 1, P.Correct ∧ P.cost ≤ 1)
    (hstep : ∀ m p : ℕ, ∀ P : MatrixAlgorithm F m p m, P.Correct →
      ∃ Q : MatrixAlgorithm F (a * m) (b * p) (a * m), Q.Correct ∧
        Q.cost ≤ R * P.cost + K * (m * p + m ^ 2)) :
    RectangularAdmissibleExponent F k τ := by
  apply rectangularAdmissibleExponent_of_power_costs ha hk hab hτ
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := rectangularBlockCost_bound (K := K) ha hε hR hin hout
  refine ⟨C, hC, ?_⟩
  intro t
  obtain ⟨P, hP, hcost⟩ := rectangular_power_programs_of_block_step hscalar hstep t
  exact ⟨P, hP, (by exact_mod_cast hcost : (P.cost : ℝ) ≤
    (rectangularBlockCost a b R K t : ℝ)).trans (hbound t)⟩

end MatrixMultiplication.Arithmetic

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Rectangular_Recursion
attribute [-simp] _root_.OAI.MatrixMultiplication.Foundation.ExecutionPairingBudget.MatrixCoordinates.standard_tensor _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.ofRankAtMost_polynomial _root_.OAI.MatrixMultiplication.RecursiveCompletion.complete_tensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rectangular matrix multiplication algorithms and their asymptotic exponents. -/

noncomputable section

namespace MatrixMultiplication

open MatrixMultiplication.Foundation

namespace Tensor

open MatrixMultiplication.Foundation.Tensor

theorem rectangular_rank_of_injective
    {K A B C A' B' C' : Type*} [CommSemiring K]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq A'] [DecidableEq B'] [DecidableEq C'] {R : ℕ}
    (h : RankAtMost (matrixCoefficients (K := K) A B C) R)
    (f : A' → A) (hf : Function.Injective f)
    (g : B' → B) (hg : Function.Injective g)
    (j : C' → C) (hj : Function.Injective j) :
    RankAtMost (matrixCoefficients (K := K) A' B' C') R := by
  have hp := h.pullback (fun x : A' × B' => (f x.1, g x.2))
    (fun y : B' × C' => (g y.1, j y.2))
    (fun z : C' × A' => (j z.1, f z.2))
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  funext x y z
  simp only [pullback, matrixCoefficients, hf.eq_iff, hg.eq_iff, hj.eq_iff]

theorem rectangular_directSum_rank_of_injective
    {K ι κ A B C A' B' C' : Type*} [CommSemiring K]
    [DecidableEq ι] [DecidableEq κ]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq A'] [DecidableEq B'] [DecidableEq C'] {R : ℕ}
    (h : RankAtMost (directSum (fun _ : ι => matrixCoefficients (K := K) A B C)) R)
    (e : κ → ι) (he : Function.Injective e)
    (f : A' → A) (hf : Function.Injective f)
    (g : B' → B) (hg : Function.Injective g)
    (j : C' → C) (hj : Function.Injective j) :
    RankAtMost (directSum (fun _ : κ => matrixCoefficients (K := K) A' B' C')) R := by
  have hp := h.pullback
    (fun x : κ × (A' × B') => (e x.1, (f x.2.1, g x.2.2)))
    (fun y : κ × (B' × C') => (e y.1, (g y.2.1, j y.2.2)))
    (fun z : κ × (C' × A') => (e z.1, (j z.2.1, f z.2.2)))
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  funext x y z
  simp only [pullback, directSum, matrixCoefficients,
    he.eq_iff, hf.eq_iff, hg.eq_iff, hj.eq_iff]

theorem rectangular_directSum_power_rank {K : Type*} [CommSemiring K]
    {a b c L R t : ℕ}
    (h : RankAtMost (power (directSum (fun _ : Fin L =>
      matrixCoefficients (K := K) (Fin a) (Fin b) (Fin c))) t) R) :
    RankAtMost (directSum (fun _ : Fin (L ^ t) =>
      matrixCoefficients (K := K) (Fin (a ^ t)) (Fin (b ^ t)) (Fin (c ^ t)))) R := by
  have hmatrix := matrixCoefficients_directSum_rank_of_power h
  let tags : Fin (L ^ t) ≃ (Fin t → Fin L) := Fintype.equivOfCardEq (by simp)
  let rows : Fin (a ^ t) ≃ (Fin t → Fin a) := Fintype.equivOfCardEq (by simp)
  let inner : Fin (b ^ t) ≃ (Fin t → Fin b) := Fintype.equivOfCardEq (by simp)
  let cols : Fin (c ^ t) ≃ (Fin t → Fin c) := Fintype.equivOfCardEq (by simp)
  exact rectangular_directSum_rank_of_injective hmatrix tags tags.injective
    rows rows.injective inner inner.injective cols cols.injective

theorem rectangular_pow_batchRank {K : Type*} [CommSemiring K]
    {a b c L r : ℕ} (hL : 0 < L)
    (hbatch : RankAtMost (directSum (fun _ : Fin L =>
      matrixCoefficients (K := K) (Fin a) (Fin b) (Fin c))) r) :
    ∀ t : ℕ, RankAtMost
      (matrixCoefficients (K := K) (Fin (a ^ t)) (Fin (b ^ t)) (Fin (c ^ t)))
      (batchRank L r t) := by
  intro t
  induction t with
  | zero => exact matrixCoefficients_fin_one_rank (K := K)
  | succ t ih =>
    let rows : Fin (a ^ (t + 1)) ≃ Fin (a ^ t) × Fin a :=
      Fintype.equivOfCardEq (by simp [pow_succ])
    let inner : Fin (b ^ (t + 1)) ≃ Fin (b ^ t) × Fin b :=
      Fintype.equivOfCardEq (by simp [pow_succ])
    let cols : Fin (c ^ (t + 1)) ≃ Fin (c ^ t) × Fin c :=
      Fintype.equivOfCardEq (by simp [pow_succ])
    have hp := matrixCoefficients_rank_of_product (ih.batch_product_ceiling hbatch hL)
    have hr := rectangular_rank_of_injective hp
      rows rows.injective inner inner.injective cols cols.injective
    simpa only [batchRank_succ] using hr

theorem rectangular_directSum_cyclic_rank
    {K ι A B C : Type*} [CommSemiring K]
    [DecidableEq ι] [DecidableEq A] [DecidableEq B] [DecidableEq C] {r : ℕ}
    (h : RankAtMost (directSum (fun _ : ι => matrixCoefficients (K := K) A B C)) r) :
    RankAtMost (directSum (fun _ : ι => matrixCoefficients (K := K) B C A)) r := by
  rcases h with ⟨a, b, c, heq⟩
  refine ⟨b, c, a, ?_⟩
  funext x y z
  have hcyc : directSum (fun _ : ι => matrixCoefficients (K := K) B C A) x y z =
      directSum (fun _ : ι => matrixCoefficients (K := K) A B C) z x y := by
    have htags : (x.1 = y.1 ∧ x.1 = z.1) ↔ (z.1 = x.1 ∧ z.1 = y.1) := by
      constructor
      · rintro ⟨hxy, hxz⟩
        exact ⟨hxz.symm, hxz.symm.trans hxy⟩
      · rintro ⟨hzx, hzy⟩
        exact ⟨hzx.symm.trans hzy, hzx.symm⟩
    simp only [directSum, htags]
    split_ifs
    · exact (matrixCoefficients_cyclic (K := K) x.2 y.2 z.2).symm
    · rfl
  rw [hcyc, congrFun (congrFun (congrFun heq z) x) y]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [rankOne]
  ring

theorem rectangular_directSum_rank_lower {K : Type*} [Field K]
    {a b L r : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : RankAtMost (directSum (fun _ : Fin L =>
      matrixCoefficients (K := K) (Fin a) (Fin b) (Fin a))) r) :
    L * a ^ 2 ≤ r ∧ L * (a * b) ≤ r := by
  let : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
  let : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
  constructor
  · simpa only [Fintype.card_fin, pow_two] using
      directSum_matrixCoefficients_rank_lower h
  · simpa only [Fintype.card_fin] using
      directSum_matrixCoefficients_rank_lower (rectangular_directSum_cyclic_rank h)

end Tensor
end MatrixMultiplication

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Tensor_FieldCoefficientExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.FieldCoefficientExtraction

variable {F X Y Z : Type*}

theorem coeff_triple [CommSemiring F] (a b c : Polynomial F) (d : ℕ) :
    (a * b * c).coeff d =
      ∑ i : Fin (d + 1), ∑ j : Fin (d + 1),
        (if j.val ≤ d - i.val then a.coeff (d - i.val - j.val) else 0) *
          b.coeff j.val * c.coeff i.val := by
  classical
  rw [show a * b * c = c * (b * a) by ring]
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    (if j ≤ d - i.val then a.coeff (d - i.val - j) else 0) *
      b.coeff j * c.coeff i.val) (d + 1)]
  symm
  calc
    (∑ j ∈ Finset.range (d + 1),
        (if j ≤ d - i.val then a.coeff (d - i.val - j) else 0) *
          b.coeff j * c.coeff i.val) =
        ∑ j ∈ Finset.range (d - i.val + 1),
          (if j ≤ d - i.val then a.coeff (d - i.val - j) else 0) *
            b.coeff j * c.coeff i.val := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro j hj hjnot
      have h : ¬ j ≤ d - i.val := by
        simpa only [Finset.mem_range, Nat.lt_succ_iff] using hjnot
      simp [h]
    _ = ∑ j ∈ Finset.range (d - i.val + 1),
        c.coeff i.val * (b.coeff j * a.coeff (d - i.val - j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [ite_eq_left (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
      ring

theorem rankAtMost_coeff [CommSemiring F]
    {P : Tensor (Polynomial F) X Y Z} {r : ℕ}
    (hP : Tensor.RankAtMost P r) (d : ℕ) :
    Tensor.RankAtMost (fun x y z => (P x y z).coeff d) ((d + 1) ^ 2 * r) := by
  classical
  rcases hP with ⟨a, b, c, rfl⟩
  let aa : (Fin r × Fin (d + 1) × Fin (d + 1)) → X → F :=
    fun v x => if v.2.2.val ≤ d - v.2.1.val then
      (a v.1 x).coeff (d - v.2.1.val - v.2.2.val) else 0
  let bb : (Fin r × Fin (d + 1) × Fin (d + 1)) → Y → F :=
    fun v y => (b v.1 y).coeff v.2.2.val
  let cc : (Fin r × Fin (d + 1) × Fin (d + 1)) → Z → F :=
    fun v z => (c v.1 z).coeff v.2.1.val
  have heq : (fun x y z => (∑ j, Tensor.rankOne (a j) (b j) (c j) x y z).coeff d) =
      fun x y z => ∑ v, Tensor.rankOne (aa v) (bb v) (cc v) x y z := by
    funext x y z
    simp only [Polynomial.finsetSum_coeff, Tensor.rankOne, Fintype.sum_prod_type,
      coeff_triple, aa, bb, cc]
  rw [heq]
  simpa only [Fintype.card_prod, Fintype.card_fin, pow_two, Nat.mul_comm,
    Nat.mul_left_comm, Nat.mul_assoc] using Tensor.rankAtMost_sum_rankOne aa bb cc

theorem rank_power [Field F] {T : Tensor F X Y Z} {r d D : ℕ}
    (A : Tensor.PolynomialApproximation T r d D) (n : ℕ) :
    Tensor.RankAtMost (Tensor.power T n) ((d * n + 1) ^ 2 * r ^ n) := by
  have h := rankAtMost_coeff (A.power n).rank_bound (d * n)
  have heq : (fun x y z => ((A.power n).polynomial x y z).coeff (d * n)) =
      Tensor.power T n := by
    funext x y z
    exact (A.power n).leading x y z
  rw [heq] at h
  exact h

end MatrixMultiplication.FieldCoefficientExtraction

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Rectangular_ASI
attribute [-simp] _root_.OAI.MatrixMultiplication.Arithmetic.rectangularOmega_zero _root_.OAI.MatrixMultiplication.Foundation.ExecutionPairingBudget.MatrixCoordinates.standard_tensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rectangular matrix multiplication algorithms and their asymptotic exponents. -/

noncomputable section

namespace MatrixMultiplication

open MatrixMultiplication.Foundation

namespace Arithmetic

variable {F : Type*} [Field F]

theorem rectangularAdmissibleExponent_of_rankAtMost
    {a b R : ℕ} (ha : 2 ≤ a) {k τ : ℝ} (hk : 0 ≤ k)
    (hab : (a : ℝ) ^ k ≤ (b : ℝ))
    (hRank : MatrixMultiplication.Foundation.Tensor.RankAtMost
      (MatrixMultiplication.Foundation.Tensor.matrixCoefficients (K := F) (Fin a) (Fin b) (Fin a)) R)
    (hτ : 0 ≤ τ) (hR : (R : ℝ) ≤ (a : ℝ) ^ τ)
    (hin : (a * b : ℕ) ≤ (a : ℝ) ^ τ)
    (hout : (a : ℝ) ^ (2 : ℕ) ≤ (a : ℝ) ^ τ) :
    RectangularAdmissibleExponent F k τ := by
  apply rectangularAdmissibleExponent_of_block_step
    (K := 2 * R * (2 * (a * b) + a ^ 2)) ha hk hab hτ hR hin hout
  · exact ⟨scalarAlgorithm F, scalarAlgorithm_correct F, (scalarAlgorithm_cost F).le⟩
  · intro m p P hP
    obtain ⟨Q, hQ, hcost⟩ := RecursiveBlock.rank_block_step hRank P hP
    refine ⟨Q, hQ, ?_⟩
    rw [hcost]
    nlinarith [Nat.zero_le (2 * R * (2 * (a * b) * m ^ 2 + a ^ 2 * (m * p)))]

theorem rectangular_rpow_omega_le_of_rankAtMost
    {a b R : ℕ} {B k : ℝ} (ha : 2 ≤ a) (hk : 0 ≤ k)
    (hab : (a : ℝ) ^ k ≤ (b : ℝ))
    (hRank : MatrixMultiplication.Foundation.Tensor.RankAtMost
      (MatrixMultiplication.Foundation.Tensor.matrixCoefficients (K := F) (Fin a) (Fin b) (Fin a)) R)
    (hout : (a : ℝ) ^ (2 : ℕ) ≤ B) (hin : (a * b : ℕ) ≤ B)
    (hR : (R : ℝ) ≤ B) :
    (a : ℝ) ^ rectangularOmega F k ≤ B := by
  have ha1 : 1 < (a : ℝ) := by exact_mod_cast (by omega : 1 < a)
  have ha0 : 0 < (a : ℝ) := lt_trans zero_lt_one ha1
  have hB : 0 < B := (sq_pos_of_pos ha0).trans_le hout
  have hpow : (a : ℝ) ^ Real.logb a B = B :=
    Real.rpow_logb ha0 (ne_of_gt ha1) hB
  have hτ : 2 ≤ Real.logb (a : ℝ) B := by
    apply (Real.le_logb_iff_rpow_le ha1 hB).mpr
    simpa only [Real.rpow_two] using hout
  have hadm := rectangularAdmissibleExponent_of_rankAtMost ha hk hab hRank
    (by linarith : 0 ≤ Real.logb (a : ℝ) B)
    (hR.trans_eq hpow.symm) (hin.trans_eq hpow.symm) (hout.trans_eq hpow.symm)
  exact (Real.rpow_le_rpow_of_exponent_le ha1.le
    (rectangularOmega_le_of_admissibleExponent hadm)).trans_eq hpow

theorem rectangular_rpow_omega_le_of_rank_growth
    {a b : ℕ} {q C k : ℝ} (ha : 2 ≤ a) (hk : 0 ≤ k)
    (hab : (a : ℝ) ^ k ≤ (b : ℝ))
    (hout : (a : ℝ) ^ (2 : ℕ) ≤ q) (hin : (a * b : ℕ) ≤ q)
    (R : ℕ → ℕ)
    (hRank : ∀ t, MatrixMultiplication.Foundation.Tensor.RankAtMost
      (MatrixMultiplication.Foundation.Tensor.matrixCoefficients (K := F)
        (Fin (a ^ t)) (Fin (b ^ t)) (Fin (a ^ t))) (R t))
    (hcost : ∀ t, (R t : ℝ) ≤ C * q ^ t) :
    (a : ℝ) ^ rectangularOmega F k ≤ q := by
  have ha0 : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
  have hq0 : 0 ≤ q := (sq_nonneg (a : ℝ)).trans hout
  apply power_le_of_forall_pow_le_mul_pow hq0 (C := max 1 C)
  intro t ht
  have hat : 2 ≤ a ^ t := ha.trans (le_self_pow (by omega) (Nat.ne_of_gt ht))
  have habt : ((a ^ t : ℕ) : ℝ) ^ k ≤ ((b ^ t : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Nat.cast_pow, ← Real.rpow_pow_comm ha0]
    exact pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg a) k) hab t
  have hbase : ((a ^ t : ℕ) : ℝ) ^ (2 : ℕ) ≤ max 1 C * q ^ t := by
    calc
      ((a ^ t : ℕ) : ℝ) ^ (2 : ℕ) = ((a : ℝ) ^ (2 : ℕ)) ^ t := by
        rw [Nat.cast_pow, ← pow_mul, ← pow_mul, Nat.mul_comm t 2]
      _ ≤ q ^ t := by gcongr
      _ ≤ max 1 C * q ^ t := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) C) (pow_nonneg hq0 t)
  have hinput : ((a ^ t * b ^ t : ℕ) : ℝ) ≤ max 1 C * q ^ t := by
    calc
      ((a ^ t * b ^ t : ℕ) : ℝ) = (((a * b : ℕ) : ℝ)) ^ t := by
        simp only [Nat.cast_mul, Nat.cast_pow, mul_pow]
      _ ≤ q ^ t := pow_le_pow_left₀ (Nat.cast_nonneg _) hin t
      _ ≤ max 1 C * q ^ t := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) C) (pow_nonneg hq0 t)
  have hcost' : (R t : ℝ) ≤ max 1 C * q ^ t :=
    (hcost t).trans (mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) C)
      (pow_nonneg hq0 t))
  have h := rectangular_rpow_omega_le_of_rankAtMost hat hk habt
    (hRank t) hbase hinput hcost'
  simpa only [Nat.cast_pow, ← Real.rpow_pow_comm ha0] using h

theorem equalRectangular_inequality {a b L r : ℕ} {k : ℝ}
    (ha : 2 ≤ a) (hk : 0 ≤ k) (hab : (a : ℝ) ^ k ≤ (b : ℝ))
    (hbatch : MatrixMultiplication.Foundation.Tensor.RankAtMost
      (MatrixMultiplication.Foundation.Tensor.directSum (fun _ : Fin L =>
        MatrixMultiplication.Foundation.Tensor.matrixCoefficients (K := F)
          (Fin a) (Fin b) (Fin a))) r) :
    (L : ℝ) * (a : ℝ) ^ rectangularOmega F k ≤ (r : ℝ) := by
  by_cases hL0 : L = 0
  · subst L
    simp
  have hL : 0 < L := Nat.pos_of_ne_zero hL0
  have ha0 : 0 < a := by omega
  have hb0 : 0 < b := by
    have hbR : (0 : ℝ) < (b : ℝ) :=
      (Real.rpow_pos_of_pos (by exact_mod_cast ha0) k).trans_le hab
    exact_mod_cast hbR
  have hlower := Tensor.rectangular_directSum_rank_lower ha0 hb0 hbatch
  have hLR : 0 < (L : ℝ) := by exact_mod_cast hL
  have hout : (a : ℝ) ^ (2 : ℕ) ≤ (r : ℝ) / (L : ℝ) := by
    apply (le_div_iff₀ hLR).mpr
    have hh : (L : ℝ) * (a : ℝ) ^ (2 : ℕ) ≤ (r : ℝ) := by exact_mod_cast hlower.1
    simpa only [mul_comm] using hh
  have hin : ((a * b : ℕ) : ℝ) ≤ (r : ℝ) / (L : ℝ) := by
    apply (le_div_iff₀ hLR).mpr
    have hh : (L : ℝ) * ((a * b : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast hlower.2
    simpa only [mul_comm] using hh
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hq : 1 < (r : ℝ) / (L : ℝ) := by nlinarith
  have hcost := affine_recurrence_bound (fun t => (batchRank L r t : ℝ))
    ((r : ℝ) / (L : ℝ)) (r : ℝ) hq (Nat.cast_nonneg r)
    (fun t => batchRank_succ_le_affine hL r t)
  have hbound : (a : ℝ) ^ rectangularOmega F k ≤ (r : ℝ) / (L : ℝ) := by
    apply rectangular_rpow_omega_le_of_rank_growth
      (C := (batchRank L r 0 : ℝ) + (r : ℝ) / ((r : ℝ) / (L : ℝ) - 1))
      ha hk hab hout hin (batchRank L r)
    · exact Tensor.rectangular_pow_batchRank hL hbatch
    · intro t
      exact (hcost t).trans_eq (mul_comm _ _)
  simpa only [mul_comm] using (le_div_iff₀ hLR).mp hbound

theorem power_le_of_forall_pow_le_square_linear_mul_pow (d : ℕ) {x r : ℝ}
    (hr : 0 ≤ r)
    (h : ∀ n : ℕ, 0 < n → x ^ n ≤ ((d * n + 1 : ℕ) : ℝ) ^ 2 * r ^ n) :
    x ≤ r := by
  apply power_le_of_forall_pow_le_linear_mul_pow (2 * d) hr
  intro n hn
  apply le_of_pow_le_pow_left₀ (by decide : (2 : ℕ) ≠ 0)
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr n))
  have he := h (n * 2) (Nat.mul_pos hn (by decide))
  have hcount : d * (n * 2) + 1 = 2 * d * n + 1 := by ring
  simpa only [pow_mul, hcount, mul_pow] using he

theorem equalRectangular_inequality_of_polynomialApproximation
    {a b L r d D : ℕ} {k : ℝ}
    (ha : 2 ≤ a) (hk : 0 ≤ k) (hab : (a : ℝ) ^ k ≤ (b : ℝ))
    (P : MatrixMultiplication.Foundation.Tensor.PolynomialApproximation
      (MatrixMultiplication.Foundation.Tensor.directSum (fun _ : Fin L =>
        MatrixMultiplication.Foundation.Tensor.matrixCoefficients (K := F)
          (Fin a) (Fin b) (Fin a))) r d D) :
    (L : ℝ) * (a : ℝ) ^ rectangularOmega F k ≤ (r : ℝ) := by
  apply power_le_of_forall_pow_le_square_linear_mul_pow d (Nat.cast_nonneg r)
  intro t ht
  have hat : 2 ≤ a ^ t := ha.trans (le_self_pow (by omega) (Nat.ne_of_gt ht))
  have habt : ((a ^ t : ℕ) : ℝ) ^ k ≤ ((b ^ t : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Nat.cast_pow, ← Real.rpow_pow_comm (Nat.cast_nonneg a)]
    exact pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg a) k) hab t
  have h := equalRectangular_inequality hat hk habt
    (Tensor.rectangular_directSum_power_rank (FieldCoefficientExtraction.rank_power P t))
  simpa only [Nat.cast_pow, Nat.cast_mul, mul_pow,
    ← Real.rpow_pow_comm (Nat.cast_nonneg a)] using h

theorem equalRectangular_log_inequality_of_polynomialApproximation
    {a b L r d D : ℕ} {k : ℝ}
    (ha : 2 ≤ a) (hL : 0 < L) (hk : 0 ≤ k)
    (hab : (a : ℝ) ^ k ≤ (b : ℝ))
    (P : MatrixMultiplication.Foundation.Tensor.PolynomialApproximation
      (MatrixMultiplication.Foundation.Tensor.directSum (fun _ : Fin L =>
        MatrixMultiplication.Foundation.Tensor.matrixCoefficients (K := F)
          (Fin a) (Fin b) (Fin a))) r d D) :
    rectangularOmega F k * Real.log (a : ℝ) ≤ Real.log (r : ℝ) - Real.log (L : ℝ) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hpow := Real.rpow_pos_of_pos ha0 (rectangularOmega F k)
  have hbound := equalRectangular_inequality_of_polynomialApproximation ha hk hab P
  have hlog := Real.log_le_log (mul_pos hL0 hpow) hbound
  rw [Real.log_mul (ne_of_gt hL0) (ne_of_gt hpow), Real.log_rpow ha0] at hlog
  linarith

end Arithmetic
end MatrixMultiplication

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Rectangular_RateLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rectangular matrix multiplication algorithms and their asymptotic exponents. -/

noncomputable section

namespace MatrixMultiplication.RectangularRateLimit

open Filter
open scoped Topology

theorem eventually_two_le_of_positive_log_rate
    {a : ℕ → ℕ} {scale : ℕ → ℝ} {A : ℝ}
    (scale_positive : ∀ᶠ n in atTop, 0 < scale n)
    (rate : Tendsto (fun n => Real.log (a n : ℝ) / scale n) atTop (𝓝 A))
    (positive : 0 < A) : ∀ᶠ n in atTop, 2 ≤ a n := by
  filter_upwards [rate.eventually_const_lt positive, scale_positive] with n hn hs
  have hlog : 0 < Real.log (a n : ℝ) := (div_pos_iff_of_pos_right hs).mp hn
  have ha : (1 : ℝ) < a n := (Real.log_pos_iff (Nat.cast_nonneg _)).mp hlog
  have : 1 < a n := by exact_mod_cast ha
  omega

theorem eventually_aspect_of_rate_gap
    {a b : ℕ → ℕ} {scale : ℕ → ℝ} {A B k : ℝ}
    (a_positive : ∀ n, 0 < a n) (b_positive : ∀ n, 0 < b n)
    (scale_positive : ∀ᶠ n in atTop, 0 < scale n)
    (a_rate : Tendsto (fun n => Real.log (a n : ℝ) / scale n) atTop (𝓝 A))
    (b_rate : Tendsto (fun n => Real.log (b n : ℝ) / scale n) atTop (𝓝 B))
    (gap : k * A < B) : ∀ᶠ n in atTop, (a n : ℝ) ^ k ≤ (b n : ℝ) := by
  filter_upwards [(a_rate.const_mul k).eventually_lt b_rate gap, scale_positive]
    with n hn hs
  have hlog : k * Real.log (a n : ℝ) < Real.log (b n : ℝ) := by
    apply (div_lt_div_iff_of_pos_right hs).mp
    simpa only [mul_div_assoc] using hn
  have ha : (0 : ℝ) < a n := Nat.cast_pos.mpr (a_positive n)
  have hb : (0 : ℝ) < b n := Nat.cast_pos.mpr (b_positive n)
  apply le_of_lt
  apply (Real.log_lt_log_iff (Real.rpow_pos_of_pos ha k) hb).mp
  simpa only [Real.log_rpow ha] using hlog

theorem rate_inequality_of_log_bounds
    {a multiplicity rank : ℕ → ℕ} {scale : ℕ → ℝ} {A M R exponent : ℝ}
    (scale_positive : ∀ᶠ n in atTop, 0 < scale n)
    (a_rate : Tendsto (fun n => Real.log (a n : ℝ) / scale n) atTop (𝓝 A))
    (multiplicity_rate : Tendsto
      (fun n => Real.log (multiplicity n : ℝ) / scale n) atTop (𝓝 M))
    (rank_rate : Tendsto (fun n => Real.log (rank n : ℝ) / scale n) atTop (𝓝 R))
    (finite_bound : ∀ᶠ n in atTop,
      exponent * Real.log (a n : ℝ) ≤
        Real.log (rank n : ℝ) - Real.log (multiplicity n : ℝ)) :
    exponent * A ≤ R - M := by
  apply le_of_tendsto_of_tendsto (a_rate.const_mul exponent)
    (rank_rate.sub multiplicity_rate)
  filter_upwards [finite_bound, scale_positive] with n hn hs
  have h := div_le_div_of_nonneg_right hn hs.le
  simpa only [mul_div_assoc, sub_div] using h

theorem exponent_le_of_finite_asi
    {a b multiplicity rank : ℕ → ℕ} {scale : ℕ → ℝ}
    {A B M R k exponent : ℝ}
    (a_positive : ∀ n, 0 < a n) (b_positive : ∀ n, 0 < b n)
    (scale_positive : ∀ᶠ n in atTop, 0 < scale n)
    (a_rate : Tendsto (fun n => Real.log (a n : ℝ) / scale n) atTop (𝓝 A))
    (b_rate : Tendsto (fun n => Real.log (b n : ℝ) / scale n) atTop (𝓝 B))
    (multiplicity_rate : Tendsto
      (fun n => Real.log (multiplicity n : ℝ) / scale n) atTop (𝓝 M))
    (rank_rate : Tendsto (fun n => Real.log (rank n : ℝ) / scale n) atTop (𝓝 R))
    (positive : 0 < A) (gap : k * A < B)
    (finite_asi : ∀ n, 2 ≤ a n → (a n : ℝ) ^ k ≤ (b n : ℝ) →
      exponent * Real.log (a n : ℝ) ≤
        Real.log (rank n : ℝ) - Real.log (multiplicity n : ℝ)) :
    exponent ≤ (R - M) / A := by
  apply (le_div_iff₀ positive).mpr
  apply rate_inequality_of_log_bounds scale_positive a_rate multiplicity_rate rank_rate
  filter_upwards [eventually_two_le_of_positive_log_rate scale_positive a_rate positive,
    eventually_aspect_of_rate_gap a_positive b_positive scale_positive a_rate b_rate gap]
    with n ha hab
  exact finite_asi n ha hab

end MatrixMultiplication.RectangularRateLimit

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_ExponentConsumer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualExponentBound

open Filter
open scoped Topology

theorem target_lt_fixedAspect : (93 : ℝ) / 200 < fixedAspect := by
  norm_num [fixedAspect]

theorem fixedAspect_lt_certificate : fixedAspect < (1548637 : ℝ) / 3327360 := by
  norm_num [fixedAspect]

theorem fixedAspect_lt_dual_aspect : fixedAspect < DualWitness.aspect :=
  fixedAspect_lt_certificate.trans ComplexCertificates.dual_aspect_lower

theorem fixedAspect_mem_unit : fixedAspect ∈ Set.Icc (0 : ℝ) 1 := by
  norm_num [fixedAspect]

namespace ActualFamily

theorem omega_le {k budget : ℝ} (P : ActualFamily k budget) (hk : 0 ≤ k) :
    Arithmetic.rectangularOmega ℂ k ≤ budget := by
  have hbound := RectangularRateLimit.exponent_le_of_finite_asi
    (fun n => (P.witness n).outer_pos) (fun n => (P.witness n).inner_pos)
    P.scale_positive P.outer_limit P.inner_limit P.multiplicity_limit P.rank_limit
    P.outer_positive P.aspect_gap
    (fun n ha hab => Arithmetic.equalRectangular_log_inequality_of_polynomialApproximation
      ha (P.witness n).multiplicity_pos hk hab (P.witness n).approximation)
  exact hbound.trans ((div_le_iff₀ P.outer_positive).2 P.cost_bound)

end ActualFamily

theorem omega_eq_two_of_arbitrarily_close_families {k : ℝ} (hk : 0 ≤ k)
    (families : ∀ ε : ℝ, 0 < ε → Nonempty (ActualFamily k (2 + ε))) :
    Arithmetic.rectangularOmega ℂ k = 2 := by
  apply le_antisymm _ (Arithmetic.rectangularOmega_two_le k)
  by_contra h
  have hω : 2 < Arithmetic.rectangularOmega ℂ k := lt_of_not_ge h
  have hε : 0 < (Arithmetic.rectangularOmega ℂ k - 2) / 2 := by linarith
  obtain ⟨P⟩ := families ((Arithmetic.rectangularOmega ℂ k - 2) / 2) hε
  have hbound := P.omega_le hk
  linarith

theorem alpha_gt_target_of_arbitrarily_close_families
    (families : ∀ ε : ℝ, 0 < ε → Nonempty (ActualFamily fixedAspect (2 + ε))) :
    (93 : ℝ) / 200 < Arithmetic.complexAlpha := by
  have hω := omega_eq_two_of_arbitrarily_close_families fixedAspect_mem_unit.1 families
  exact target_lt_fixedAspect.trans_le (Arithmetic.le_complexAlpha fixedAspect_mem_unit hω)

end MatrixMultiplication.DualExponentBound

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Entropy_ConditionalContinuity
attribute [-instance] _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.labelRecordZero_subsingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

namespace MatrixMultiplication.ConditionalLabels

open MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology Classical

universe u v w
variable {A : Type u} [Fintype A] {Label : ℕ → Type v}
  [∀ n, Fintype (Label n)]

theorem refinementEntropy_eq_prefix_difference (p : FiniteLaw A)
    (labels : ∀ n, A → Label n) (depth n : ℕ) (hn : n < depth) :
    (FiniteLabelHierarchy.ofLawLabels p labels depth).refinementEntropy n =
      finiteEntropy (p.map (labelRecordOf labels (n + 1))).mass -
        finiteEntropy (p.map (labelRecordOf labels n)).mass := by
  have h := (FiniteLabelHierarchy.ofLawLabels p labels depth).prefixLaw_entropy_succ
    n (Nat.succ_le_of_lt hn)
  rw [FiniteLabelHierarchy.ofLawLabels_prefixLaw_mass,
    FiniteLabelHierarchy.ofLawLabels_prefixLaw_mass] at h
  linarith

theorem tendsto_map_entropy {J : Type w} {filter : Filter J}
    {p : J → FiniteLaw A} {q : FiniteLaw A}
    (mass : ∀ a, Tendsto (fun j => (p j).mass a) filter (𝓝 (q.mass a)))
    {B : Type*} [Fintype B] (label : A → B) :
    Tendsto (fun j => finiteEntropy ((p j).map label).mass) filter
      (𝓝 (finiteEntropy (q.map label).mass)) := by
  apply FiniteLaw.entropy_tendsto
  intro b
  simp only [FiniteLaw.map_mass]
  apply tendsto_finsetSum
  intro a _
  by_cases h : label a = b
  · simpa only [h, ite_true, if_true] using mass a
  · simp only [h, ite_false, if_false]
    exact tendsto_const_nhds

theorem tendsto_lawPairingRate {J : Type w} {filter : Filter J}
    {p : J → FiniteLaw A} {q : FiniteLaw A}
    (mass : ∀ a, Tendsto (fun j => (p j).mass a) filter (𝓝 (q.mass a)))
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (reader : Fin depth → ReaderPair) (pair : ReaderPair) :
    Tendsto (fun j => lawPairingRate (p j) labels depth reader pair) filter
      (𝓝 (lawPairingRate q labels depth reader pair)) := by
  unfold lawPairingRate pairingRate
  apply tendsto_finsetSum
  intro n _
  by_cases h : reader n = pair
  · simp only [h, ite_true, if_true,
      refinementEntropy_eq_prefix_difference _ labels depth n.val n.isLt]
    exact (tendsto_map_entropy mass (labelRecordOf labels (n.val + 1))).sub
      (tendsto_map_entropy mass (labelRecordOf labels n.val))
  · simp only [h, ite_false, if_false]
    exact tendsto_const_nhds

theorem exists_rational_law_sequence (p : FiniteLaw A) :
    ∃ q : ℕ → RationalLaw A,
      ∀ a, Tendsto (fun n => (q n).toFiniteLaw.mass a) atTop (𝓝 (p.mass a)) := by
  have hexists (n : ℕ) := p.exists_rational_approximation
    (1 / ((n : ℝ) + 1)) (by positivity)
  choose q _support close using hexists
  refine ⟨q, fun a => ?_⟩
  have hdifference : Tendsto
      (fun n => (q n).toFiniteLaw.mass a - p.mass a) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ tendsto_one_div_add_atTop_nhds_zero_nat
    intro n
    simpa only [Real.norm_eq_abs, RationalLaw.toFiniteLaw_mass] using (close n a).le
  simpa only [sub_add_cancel, zero_add] using hdifference.add_const (p.mass a)

theorem exists_rational_with_strict_margins (p : FiniteLaw A)
    (labels : ∀ n, A → Label n) (depth : ℕ) (reader : Fin depth → ReaderPair)
    {k C target : ℝ}
    (positive : 0 < lawPairingRate p labels depth reader .xy +
      lawPairingRate p labels depth reader .xz)
    (aspect : k * (lawPairingRate p labels depth reader .xy +
      lawPairingRate p labels depth reader .xz) <
      2 * lawPairingRate p labels depth reader .yz)
    (cost : 2 * C < target * (lawPairingRate p labels depth reader .xy +
      lawPairingRate p labels depth reader .xz)) :
    ∃ q : RationalLaw A,
      0 < lawPairingRate q.toFiniteLaw labels depth reader .xy +
        lawPairingRate q.toFiniteLaw labels depth reader .xz ∧
      k * (lawPairingRate q.toFiniteLaw labels depth reader .xy +
        lawPairingRate q.toFiniteLaw labels depth reader .xz) <
        2 * lawPairingRate q.toFiniteLaw labels depth reader .yz ∧
      2 * C < target * (lawPairingRate q.toFiniteLaw labels depth reader .xy +
        lawPairingRate q.toFiniteLaw labels depth reader .xz) := by
  obtain ⟨q, hq⟩ := exists_rational_law_sequence p
  have hincident := (tendsto_lawPairingRate hq labels depth reader .xy).add
    (tendsto_lawPairingRate hq labels depth reader .xz)
  have hhidden := tendsto_lawPairingRate hq labels depth reader .yz
  have hpos := hincident.eventually_const_lt positive
  have haspect := (hincident.const_mul k).eventually_lt (hhidden.const_mul 2) aspect
  have hcost := (hincident.const_mul target).eventually_const_lt cost
  obtain ⟨n, hnpos, hnaspect, hncost⟩ := (hpos.and (haspect.and hcost)).exists
  exact ⟨q n, hnpos, hnaspect, hncost⟩

end MatrixMultiplication.ConditionalLabels

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_FamilyConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualFiniteRealization

open MatrixMultiplication.Foundation CompletionHierarchyWords Filter
open scoped BigOperators Topology Classical

variable {A X Y Z : Type} [Fintype A] [Fintype X] [Fintype Y] [Fintype Z]
variable (H : ReadableHierarchy A X Y Z) (counts : A → ℕ)
variable (hD : 0 < ∑ a, counts a)
variable (complete : Function.Injective (labelRecordOf H.labels H.depth))
variable (p : FiniteLaw A)
variable (mass : ∀ a, p.mass a = (counts a : ℝ) / (∑ b, counts b : ℕ))
variable {T : Tensor ℂ X Y Z} {R d D : ℕ}
variable (source : Tensor.PolynomialApproximation T R d D) (hR : 0 < R)
variable (supported : ∀ x y z, T x y z ≠ 0 →
  ∃ a, H.x a = x ∧ H.y a = y ∧ H.z a = z)
variable (unit : ∀ a, T (H.x a) (H.y a) (H.z a) = 1)

include complete source hR supported unit in

theorem arbitrarily_close_families_of_exact_incident {k : ℝ}
    (log_positive : 0 < Real.log R)
    (incident : pairRate H p .xy + pairRate H p .xz = Real.log R)
    (aspect : k * (pairRate H p .xy + pairRate H p .xz) < 2 * pairRate H p .yz) :
    ∀ ε : ℝ, 0 < ε → Nonempty (DualExponentBound.ActualFamily k (2 + ε)) := by
  intro ε hε
  have positive : 0 < pairRate H p .xy + pairRate H p .xz := by
    rw [incident]
    exact log_positive
  have cost : 2 * Real.log R < (2 + ε) * (pairRate H p .xy + pairRate H p .xz) := by
    rw [incident]
    nlinarith
  obtain ⟨q, hpositive, haspect, hcost⟩ :=
    ConditionalLabels.exists_rational_with_strict_margins p H.labels H.depth
      (fun n => H.pair n.val) positive aspect cost
  obtain ⟨population, hpopulation, hmass⟩ := q.exists_type_representation
  refine ⟨actualFamily H population hpopulation complete q.toFiniteLaw ?_
    source hR supported unit hpositive haspect hcost.le⟩
  intro a
  exact (hmass a).symm

end MatrixMultiplication.DualFiniteRealization

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_InformationSchedule
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.labelRecordZero_subsingleton
attribute [-simp] _root_.OAI.MatrixMultiplication.CW75ReorderedExecution.pairingProduct_zero _root_.OAI.MatrixMultiplication.CompletionExecution.pairingProduct_zero _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_auxiliaryRank _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_columns _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_inner _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_multiplicity _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_occurrences _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_rows _root_.OAI.MatrixMultiplication.CompletionProductLaws.independentProduct_mass _root_.OAI.MatrixMultiplication.CompletionProductLaws.sigmaJoint_mass _root_.OAI.MatrixMultiplication.CompletionTermination.retainedLeafEquiv_coordinates _root_.OAI.MatrixMultiplication.ConditionalLabels.normalizedCountLaw_mass _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_inner _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_multiplicity _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_outer _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_rank _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_x _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_y _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_z _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.appendCode_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.appendPrefix_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.decodedFine_eq_geometryDecode _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.encodeSourceWord_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.finePrefix_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.mem_conditionalFinset _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.oldPrefix_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.rootPrefixWord_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourcePrefixEquiv_apply_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourcePrefixEquiv_symm_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourceSymbol_encodeSourceWord _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourceSymbol_record
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.CompletionLabels.TopologicalFlatten.Program

open MatrixMultiplication.Foundation RecursiveCompletion DualInformation

universe u v w z

variable {A : Type u} [Fintype A] {Coord : Color → Type v}
  [Fintype (Coord .B)] {Context : Type z} {Code : Type w} [Fintype Code]
  {depth : ℕ}

theorem incident_rate_eq_x_entropy (s : Program A Coord Context Code depth)
    (p : FiniteLaw A) (complete : s.Complete) (ctx : Context)
    (context_constant : ∀ a, s.context a = ctx)
    (independent : ∀ n : Fin depth, s.pair n.val = .yz →
      ConditionalIndependent p (labelRecordOf s.labels n.val)
        (s.labels n.val) (s.view .B)) :
    ConditionalLabels.lawPairingRate p s.labels depth (fun n => s.pair n.val) .xy +
      ConditionalLabels.lawPairingRate p s.labels depth (fun n => s.pair n.val) .xz =
        finiteEntropy (p.map (s.view .B)).mass := by
  have hinj : Function.Injective (labelRecordOf s.labels depth) := by
    intro a b h
    apply complete a b ((context_constant a).trans (context_constant b).symm)
    intro n hn
    exact label_eq_of_record_eq s.labels h hn
  apply incident_rate_eq_coordinate_entropy p s.labels depth (fun n => s.pair n.val)
    (s.view .B) hinj ?_ independent
  intro n hn
  have hs : .B = firstSide (s.pair n.val) := by
    cases hr : s.pair n.val <;> simp_all [firstSide]
  refine ⟨fun rx => s.read n.val .B ctx (recordArray n.val rx.1) rx.2, ?_⟩
  intro a
  change s.read n.val .B ctx (recordArray n.val (labelRecordOf s.labels n.val a))
    (s.view .B a) = s.labels n.val a
  rw [recordArray_labelRecordOf]
  rw [← context_constant a]
  exact s.readable n.val n.isLt a .B (Or.inl hs)

end MatrixMultiplication.CompletionLabels.TopologicalFlatten.Program

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_InformationLabelConditioning
attribute [-simp] _root_.OAI.MatrixMultiplication.CompletionProductLaws.independentProduct_mass _root_.OAI.MatrixMultiplication.CompletionProductLaws.sigmaJoint_mass _root_.OAI.MatrixMultiplication.ConditionalLabels.normalizedCountLaw_mass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualInformation

open MatrixMultiplication.Foundation CompletionLaws
attribute [local instance] Classical.propDecidable Classical.decEq

variable {A L X : Type*} [Fintype A] [Fintype L] [Fintype X]

theorem mass_factorization_const_iff (p : FiniteLaw A)
    (label : A → L) (x : A → X) :
    ConditionalMassFactorization p (fun _ => PUnit.unit) label x ↔
      ∀ l xx, (p.map (fun a => (label a, x a))).mass (l, xx) =
        (p.map label).mass l * (p.map x).mass xx := by
  classical
  constructor
  · intro h l xx
    have hf := h PUnit.unit l xx
    simpa [FiniteLaw.map_mass, Prod.mk.injEq, p.total] using hf
  · intro h r l xx
    cases r
    simpa [FiniteLaw.map_mass, Prod.mk.injEq, p.total] using h l xx

theorem conditionalMassFactorization_condition_label (p : FiniteLaw A)
    (label : A → L) (x : A → X) (Q : L → Prop)
    (h : 0 < eventMass p (fun a => Q (label a)))
    (factor : ConditionalMassFactorization p (fun _ => PUnit.unit) label x) :
    ConditionalMassFactorization (condition p (fun a => Q (label a)) h)
      (fun _ => PUnit.unit) (fun a => label a.val) (fun a => x a.val) := by
  have independent := (mass_factorization_const_iff p label x).mp factor
  have swapped : ∀ xx l,
      (p.map (fun a => (x a, label a))).mass (xx, l) =
        (p.map x).mass xx * (p.map label).mass l := by
    intro xx l
    have hm : (p.map (fun a => (x a, label a))).mass (xx, l) =
        (p.map (fun a => (label a, x a))).mass (l, xx) := by
      simp only [FiniteLaw.map_mass, Prod.mk.injEq, and_comm]
    rw [hm, independent l xx, mul_comm]
  apply (mass_factorization_const_iff _ _ _).mpr
  intro l xx
  have hj := condition_coordinate_mass p (fun a => (label a, x a))
    (fun v => Q v.1) h (l, xx)
  have hl := condition_coordinate_mass p label Q h l
  have hx := condition_independent_coordinate_mass p x label Q swapped h xx
  rw [hj, hl, hx]
  by_cases hQ : Q l
  · simp only [hQ, ite_true, if_true]
    rw [independent l xx]
    ring
  · simp only [hQ, ite_false, if_false, zero_mul]

end MatrixMultiplication.DualInformation

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_UniformMixtures
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype
attribute [-simp] _root_.OAI.MatrixMultiplication.CompletionTermination.retainedLeafEquiv_coordinates _root_.OAI.MatrixMultiplication.ConditionalLabels.normalizedCountLaw_mass _root_.OAI.MatrixMultiplication.DualInformation.remainingEntropy_zero _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_x _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_y _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_z
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

universe uCoord

namespace MatrixMultiplication.DualUniformMixtures

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels CompletionColorLaws
open CompletionLaws DualEntropyHelpers
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

variable {X Y Z : Type uCoord} {U A : Type*} [Fintype X] [Fintype Y] [Fintype Z]
  [Fintype U] [Fintype A]

theorem uniform_coordinate_card_pos (p : FiniteLaw A) (f : A → U)
    (P : U → Prop) (h : UniformCoordinate p f P) :
    0 < Fintype.card {x // P x} := by
  by_contra hn
  have hz : Fintype.card {x // P x} = 0 := Nat.eq_zero_of_not_pos hn
  have ht := (p.map f).total
  have hmass : ∀ x, (p.map f).mass x =
      if P x then (Fintype.card {x // P x} : ℝ)⁻¹ else 0 := h
  simp_rw [hmass] at ht
  simp [hz] at ht

theorem colorMix_map_comp_mass (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) (f : Leaf S → U) (x : U) :
    ((colorMix S center output pc po α hα hα').map f).mass x =
      α * (pc.map (fun a => f a.val)).mass x +
        (1 - α) * (po.map (fun a => f a.val)).mass x := by
  rw [colorMix_map_mass, map_comp_mass, map_comp_mass]

theorem colorMix_map_of_common (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) (f : Leaf S → U)
    (hcommon : ∀ x, (pc.map (fun a => f a.val)).mass x =
      (po.map (fun a => f a.val)).mass x) (x : U) :
    ((colorMix S center output pc po α hα hα').map f).mass x =
      (pc.map (fun a => f a.val)).mass x := by
  rw [colorMix_map_comp_mass, ← hcommon x]
  ring

theorem colorMix_uniform_common (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) (P : X → Prop)
    (hc : UniformCoordinate pc (fun a => a.val.val.1) P)
    (ho : UniformCoordinate po (fun a => a.val.val.1) P) :
    UniformCoordinate (colorMix S center output pc po α hα hα')
      (fun a => a.val.1) P := by
  intro x
  rw [colorMix_map_of_common S center output pc po α hα hα' (fun a => a.val.1)
    (fun x => (hc x).trans (ho x).symm)]
  exact hc x

theorem colorMix_uniform_complement (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) (P : X → Prop)
    (hc : UniformCoordinate pc (fun a => a.val.val.1) P)
    (ho : UniformCoordinate po (fun a => a.val.val.1) (fun x => ¬ P x))
    (hweight : α = (Fintype.card {x // P x} : ℝ) / Fintype.card X) :
    UniformCoordinate (colorMix S center output pc po α hα hα')
      (fun a => a.val.1) (fun _ => True) := by
  have hp : (Fintype.card {x // P x} : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr (uniform_coordinate_card_pos pc _ P hc)).ne'
  have hn : (Fintype.card {x // ¬ P x} : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr (uniform_coordinate_card_pos po _ _ ho)).ne'
  have hsumNat : Fintype.card {x // P x} + Fintype.card {x // ¬ P x} =
      Fintype.card X := by
    rw [Fintype.card_subtype_compl]
    exact Nat.add_sub_of_le (Fintype.card_subtype_le P)
  have hsum : (Fintype.card {x // P x} : ℝ) + Fintype.card {x // ¬ P x} =
      Fintype.card X := by exact_mod_cast hsumNat
  have hX : (Fintype.card X : ℝ) ≠ 0 := by
    have : 0 < Fintype.card X := lt_of_lt_of_le
      (uniform_coordinate_card_pos pc _ P hc) (Fintype.card_subtype_le P)
    exact (Nat.cast_pos.mpr this).ne'
  have hrest : 1 - α =
      (Fintype.card {x // ¬ P x} : ℝ) / Fintype.card X := by
    rw [hweight, one_sub_div hX, show (Fintype.card X : ℝ) -
      Fintype.card {x // P x} = Fintype.card {x // ¬ P x} by linarith]
  intro x
  rw [colorMix_map_comp_mass, hc x, ho x, hrest, hweight]
  simp only [ite_true, if_true, Fintype.card_subtype_true]
  by_cases hx : P x <;> simp only [hx, not_true_eq_false, not_false_eq_true,
    ite_true, if_true, ite_false, if_false, mul_zero, zero_add, add_zero]
  · rw [div_eq_mul_inv, mul_right_comm, mul_inv_cancel₀ hp, one_mul]
  · rw [div_eq_mul_inv, mul_right_comm, mul_inv_cancel₀ hn, one_mul]

theorem colorMix_uniform_complement_reverse
    (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (rho : ℝ) (hα : 0 ≤ 1 - rho) (hα' : 1 - rho ≤ 1) (P : X → Prop)
    (hc : UniformCoordinate pc (fun a => a.val.val.1) (fun x => ¬ P x))
    (ho : UniformCoordinate po (fun a => a.val.val.1) P)
    (hweight : rho = (Fintype.card {x // P x} : ℝ) / Fintype.card X) :
    UniformCoordinate (colorMix S center output pc po (1 - rho) hα hα')
      (fun a => a.val.1) (fun _ => True) := by
  apply colorMix_uniform_complement S center output pc po (1 - rho) hα hα'
    (fun x => ¬ P x) hc
  · simpa only [not_not] using ho
  · have hsumNat : Fintype.card {x // P x} + Fintype.card {x // ¬ P x} =
        Fintype.card X := by
      rw [Fintype.card_subtype_compl]
      exact Nat.add_sub_of_le (Fintype.card_subtype_le P)
    have hsum : (Fintype.card {x // P x} : ℝ) + Fintype.card {x // ¬ P x} =
        Fintype.card X := by exact_mod_cast hsumNat
    have hX : (Fintype.card X : ℝ) ≠ 0 := by
      have : 0 < Fintype.card X := lt_of_lt_of_le
        (uniform_coordinate_card_pos po _ P ho) (Fintype.card_subtype_le P)
      exact (Nat.cast_pos.mpr this).ne'
    rw [hweight, one_sub_div hX, show (Fintype.card X : ℝ) -
      Fintype.card {x // P x} = Fintype.card {x // ¬ P x} by linarith]

theorem colorSlice_color_mass (S : FlaggedTensor X Y Z) (c : Color)
    (p : FiniteLaw (ColorSlice S c)) (b : Color) :
    ((p.map Subtype.val).map (leafColor S)).mass b = if c = b then 1 else 0 := by
  rw [map_comp_mass, FiniteLaw.map_mass]
  have hc : ∀ a : ColorSlice S c, leafColor S a.val = c := fun a => a.property
  simp_rw [hc]
  by_cases h : c = b <;> simp [h, p.total]

theorem colorSlice_pair_mass (S : FlaggedTensor X Y Z) (c : Color)
    (p : FiniteLaw (ColorSlice S c)) (f : Leaf S → U) (x : U) (b : Color) :
    ((p.map Subtype.val).map (fun a => (f a, leafColor S a))).mass (x, b) =
      if c = b then (p.map (fun a => f a.val)).mass x else 0 := by
  rw [map_comp_mass, FiniteLaw.map_mass]
  have hc : ∀ a : ColorSlice S c, leafColor S a.val = c := fun a => a.property
  simp_rw [hc]
  by_cases h : c = b <;> simp [h, FiniteLaw.map_mass]

theorem colorMix_independent_common (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) (f : Leaf S → U)
    (hcommon : ∀ x, (pc.map (fun a => f a.val)).mass x =
      (po.map (fun a => f a.val)).mass x) (x : U) (b : Color) :
    ((colorMix S center output pc po α hα hα').map
      (fun a => (f a, leafColor S a))).mass (x, b) =
      ((colorMix S center output pc po α hα hα').map f).mass x *
        ((colorMix S center output pc po α hα hα').map (leafColor S)).mass b := by
  rw [colorMix_map_of_common S center output pc po α hα hα' f hcommon x]
  rw [colorMix_map_mass, colorMix_map_mass,
    colorSlice_pair_mass, colorSlice_pair_mass,
    colorSlice_color_mass, colorSlice_color_mass, ← hcommon x]
  by_cases hc : center = b <;> by_cases ho : output = b <;> simp [hc, ho] <;> ring

theorem colorMix_independent_uniform (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) (P : X → Prop)
    (hc : UniformCoordinate pc (fun a => a.val.val.1) P)
    (ho : UniformCoordinate po (fun a => a.val.val.1) P) (x : X) (b : Color) :
    ((colorMix S center output pc po α hα hα').map
      (fun a => (a.val.1, leafColor S a))).mass (x, b) =
      ((colorMix S center output pc po α hα hα').map (fun a => a.val.1)).mass x *
        ((colorMix S center output pc po α hα hα').map (leafColor S)).mass b :=
  colorMix_independent_common S center output pc po α hα hα' (fun a => a.val.1)
    (fun x => (hc x).trans (ho x).symm) x b

end MatrixMultiplication.DualUniformMixtures

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_RootIndependence
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.labelRecordZero_subsingleton
attribute [-simp] _root_.OAI.MatrixMultiplication.CompletionTermination.retainedLeafEquiv_coordinates _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_x _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_y _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_z
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualProgramIndependence

universe u w

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels
open CompletionLaws CompletionColorLaws CompletionProductLaws DualUniformProducts
open DualInformation DualInformationTransport DualUniformMixtures TopologicalFlatten
open scoped BigOperators
theorem rootColor_inj_before_three {i j : ℕ} (hi : i < 3) (hj : j < 3) :
    rootColor i = rootColor j ↔ i = j := by
  interval_cases i <;> interval_cases j <;> simp [rootColor]

private theorem completion_index_decomposition {n m depth : ℕ}
    (hn : n < 3 + m * depth) (hn3 : ¬ n < 3) :
    0 < depth ∧ n - 3 < m * depth ∧
      n = 3 + ((n - 3) / depth * depth + (n - 3) % depth) := by
  have hd : 0 < depth := by
    by_contra h
    have hz : depth = 0 := by omega
    simp only [hz, mul_zero, add_zero] at hn
    omega
  refine ⟨hd, by omega, ?_⟩
  have h : (n - 3) / depth * depth + (n - 3) % depth = n - 3 := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod (n - 3) depth
  omega

attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

variable {X Y Z : Type u} {Code : Type w} [Fintype X] [Fintype Y] [Fintype Z]
  [Fintype Code] [Inhabited Code] {depth m : ℕ}

theorem conditionalCompletionLaw_pattern_factorization (S : FlaggedTensor X Y Z)
    (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α < 1) (hm : 0 < m)
    (hcommon : ∀ x, (pc.map (fun a => a.val.val.1)).mass x =
      (po.map (fun a => a.val.val.1)).mass x) :
    ConditionalMassFactorization
      (conditionalCompletionLaw S center output pc po m hm α hα hα')
      (fun _ => (PUnit.unit : PUnit.{1})) (fun a => pattern S center m a.val)
      (fun a => a.val.val.1) := by
  let mix := colorMix S center output pc po α hα hα'.le
  have hs (c : Color) (x : X) :
      (mix.map (fun a => (leafColor S a, a.val.1))).mass (c, x) =
        (mix.map (leafColor S)).mass c * (mix.map (fun a => a.val.1)).mass x := by
    have h := colorMix_independent_common S center output pc po α hα hα'.le
      (fun a => a.val.1) hcommon x c
    simpa only [FiniteLaw.map_mass, Prod.mk.injEq, and_comm, mul_comm] using h
  have hw : ConditionalMassFactorization (iidColorLaw S center output pc po m α hα hα'.le)
      (fun _ => (PUnit.unit : PUnit.{1})) (fun a j => leafColor S (a j)) (fun a j => (a j).val.1) := by
    apply (mass_factorization_const_iff _ _ _).mpr
    exact independentProduct_independent (fun _ : Fin m => mix)
      (fun _ => leafColor S) (fun _ a => a.val.1) (fun _ => hs)
  let Q : (Fin m → Color) → Prop := fun c =>
    raisedFlag center output (fun j => c j = output) ∧
      ∀ j, c j = center ∨ c j = output
  have hcondition := conditionalMassFactorization_condition_label
    (iidColorLaw S center output pc po m α hα hα'.le)
    (fun a j => leafColor S (a j)) (fun a j => (a j).val.1) Q
    (completionEvent_mass_pos S center output pc po m hm α hα hα') hw
  let e := conditionalLeafEquiv S center output m
  let q := condition (iidColorLaw S center output pc po m α hα hα'.le)
    (completionEvent S center output m)
    (completionEvent_mass_pos S center output pc po m hm α hα hα')
  have hslot (a : {w : Fin m → Leaf S // completionEvent S center output m w}) :
      slot S center m (e.symm a).val = a.val :=
    congrArg Subtype.val (e.apply_symm_apply a)
  change ConditionalMassFactorization (q.map e.symm) _ _ _
  rw [mass_factorization_map_iff]
  apply mass_factorization_of_same_partitions q (fun _ => (PUnit.unit : PUnit.{1}))
    (fun a j => leafColor S (a.val j)) (fun a j => (a.val j).val.1)
  · intro a b
    rfl
  · intro a b
    rfl
  · intro a b
    rfl
  · exact hcondition

theorem conditionalCompletionLaw_root_factorization (S : FlaggedTensor X Y Z)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (context_eq : ∀ a, p.context a = leafColor S a)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side)
    (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α < 1) (hm : 0 < m)
    (n : ℕ) (hn : n < 3)
    (hcommon : ownerPair center output = .yz → ∀ x,
      (pc.map (fun a => a.val.val.1)).mass x =
        (po.map (fun a => a.val.val.1)).mass x)
    (hpair : (completionLocalProgram S center m p context_eq view_eq).pair n = .yz) :
    ConditionalMassFactorization
      (conditionalCompletionLaw S center output pc po m hm α hα hα')
      (fun a => labelRecordOf
        (completionLocalProgram S center m p context_eq view_eq).labels n a.val)
      (fun a => (completionLocalProgram S center m p context_eq view_eq).labels n a.val)
      (fun a => a.val.val.1) := by
  let law := conditionalCompletionLaw S center output pc po m hm α hα hα'
  let cp := completionLocalProgram S center m p context_eq view_eq
  have hroot (j : ℕ) (hj : j < 3) (a : ColorSlice (complete S center m) output) :
      cp.labels j a.val = encodePattern
        (if output = rootColor j then some (pattern S center m a.val) else none) := by
    rw [completionLocalProgram_label_root S center m p context_eq view_eq j hj, a.property]
    split_ifs <;> rfl
  by_cases hactive : output = rootColor n
  · have hp : ownerPair center output = .yz := by
      rw [completionLocalProgram_pair_root S center m p context_eq view_eq n hn,
        ← hactive] at hpair
      exact hpair
    have hprev (a b : ColorSlice (complete S center m) output) :
        labelRecordOf cp.labels n a.val = labelRecordOf cp.labels n b.val := by
      apply (labelRecordOf_eq_iff _ _ _ _).mpr
      intro j hj
      have hj3 : j < 3 := lt_trans hj hn
      have hne : output ≠ rootColor j := by
        intro he
        have hnj : n = j := (rootColor_inj_before_three hn hj3).mp (hactive.symm.trans he)
        exact (Nat.ne_of_lt hj) hnj.symm
      rw [hroot j hj3 a, hroot j hj3 b, ite_eq_right hne, ite_eq_right hne]
    apply mass_factorization_of_same_partitions law (fun _ => (PUnit.unit : PUnit.{1}))
      (fun a => pattern S center m a.val) (fun a => a.val.val.1)
    · intro a b
      exact iff_of_true rfl (hprev a b)
    · intro a b
      rw [hroot n hn a, hroot n hn b, ite_eq_left hactive, ite_eq_left hactive]
      simp only [encodePattern, Option.some.injEq, Sum.inl.injEq]
    · intro a b
      rfl
    · exact conditionalCompletionLaw_pattern_factorization S center output pc po α hα hα' hm
        (hcommon hp)
  · have hlabel : (fun a : ColorSlice (complete S center m) output => cp.labels n a.val) =
        (fun _ => encodePattern (Code := Code) none) := by
      funext a
      rw [hroot n hn a, ite_eq_right hactive]
    change ConditionalMassFactorization law _ _ _
    rw [hlabel]
    exact factorization_constant_label law _ _ _

theorem conditionalCompletionLaw_program_factorization (S : FlaggedTensor X Y Z)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (context_eq : ∀ a, p.context a = leafColor S a)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side)
    (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α < 1) (hbranch : center ≠ output ∨ α = 0)
    (hm : 0 < m)
    (hcommon : ownerPair center output = .yz → ∀ x,
      (pc.map (fun a => a.val.val.1)).mass x =
        (po.map (fun a => a.val.val.1)).mass x)
    (hc : ∀ n : Fin depth, p.pair n.val = .yz →
      ConditionalMassFactorization pc (fun a => labelRecordOf p.labels n.val a.val)
        (fun a => p.labels n.val a.val) (fun a => a.val.val.1))
    (ho : ∀ n : Fin depth, p.pair n.val = .yz →
      ConditionalMassFactorization po (fun a => labelRecordOf p.labels n.val a.val)
        (fun a => p.labels n.val a.val) (fun a => a.val.val.1))
    (n : Fin (3 + m * depth))
    (hpair : (completionLocalProgram S center m p context_eq view_eq).pair n.val = .yz) :
    ConditionalMassFactorization
      (conditionalCompletionLaw S center output pc po m hm α hα hα')
      (fun a => labelRecordOf
        (completionLocalProgram S center m p context_eq view_eq).labels n.val a.val)
      (fun a => (completionLocalProgram S center m p context_eq view_eq).labels n.val a.val)
      (fun a => a.val.val.1) := by
  by_cases hn : n.val < 3
  · exact conditionalCompletionLaw_root_factorization S p context_eq view_eq
      center output pc po α hα hα' hm n.val hn hcommon hpair
  · obtain ⟨hd, hnm, hdecomp⟩ := completion_index_decomposition n.isLt hn
    let i : Fin m := ⟨(n.val - 3) / depth, (Nat.div_lt_iff_lt_mul hd).mpr hnm⟩
    let k : ℕ := (n.val - 3) % depth
    have hk : k < depth := Nat.mod_lt _ hd
    have hsplit : n.val = 3 + (i.val * depth + k) := hdecomp
    rw [hsplit, completionLocalProgram_pair_slot S center m p context_eq view_eq i k hk] at hpair
    apply mass_factorization_of_same_partitions
      (conditionalCompletionLaw S center output pc po m hm α hα hα')
      (fun a => labelRecordOf
        (completionLocalProgram S center m p context_eq view_eq).labels
        (3 + (i.val * depth + k)) a.val)
      (fun a => (completionLocalProgram S center m p context_eq view_eq).labels
        (3 + (i.val * depth + k)) a.val)
      (fun a => a.val.val.1)
    · intro a b
      simp only [labelRecordOf_eq_iff, ← hsplit]
    · intro a b
      simp only [← hsplit]
    · intro a b
      rfl
    · exact conditionalCompletionLaw_inherited_factorization
        S p context_eq view_eq center output pc po α hα hα' hbranch hm i k hk
          (hc ⟨k, hk⟩ hpair) (ho ⟨k, hk⟩ hpair)

end MatrixMultiplication.DualProgramIndependence

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_UniformConditioning
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype
attribute [-simp] _root_.OAI.MatrixMultiplication.ConditionalLabels.normalizedCountLaw_mass _root_.OAI.MatrixMultiplication.DualInformation.remainingEntropy_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section
universe uCoord
namespace MatrixMultiplication.DualUniformConditioning

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels CompletionColorLaws
open CompletionLaws CompletionProductLaws DualEntropyHelpers
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

variable {A : Type*} {X Y Z : Type uCoord} [Fintype A] [Fintype X] [Fintype Y] [Fintype Z]

theorem eventMass_congr_support (p : FiniteLaw A) (P Q : A → Prop)
    (h : ∀ a, p.mass a ≠ 0 → (P a ↔ Q a)) : eventMass p P = eventMass p Q := by
  rw [eventMass, eventMass, sum_subtype_indicator, sum_subtype_indicator]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : p.mass a = 0
  · simp [ha]
  · rw [h a ha]

theorem condition_map_mass_congr_support (p : FiniteLaw A) (P Q : A → Prop)
    (h : ∀ a, p.mass a ≠ 0 → (P a ↔ Q a))
    (hP : 0 < eventMass p P) (hQ : 0 < eventMass p Q) (f : A → X) (x : X) :
    ((condition p P hP).map (fun a => f a.val)).mass x =
      ((condition p Q hQ).map (fun a => f a.val)).mass x := by
  rw [condition_map_mass, condition_map_mass, eventMass_congr_support p P Q h]
  congr 1
  rw [sum_subtype_indicator P (fun a => if f a = x then p.mass a else 0),
    sum_subtype_indicator Q (fun a => if f a = x then p.mass a else 0)]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : p.mass a = 0
  · simp [ha]
  · rw [h a ha]

theorem uniform_coordinate_pred_congr (p : FiniteLaw A) (f : A → X)
    (P Q : X → Prop) (h : ∀ x, P x ↔ Q x) (hp : UniformCoordinate p f P) :
    UniformCoordinate p f Q := by
  have he : P = Q := funext (fun x => propext (h x))
  simpa only [he] using hp

theorem uniform_coordinate_condition_positive (p : FiniteLaw A) (f : A → X)
    (P Q : X → Prop) (h : UniformCoordinate p f P)
    (hevent : 0 < eventMass p (fun a => Q (f a))) :
    UniformCoordinate (condition p (fun a => Q (f a)) hevent)
      (fun a => f a.val) (fun x => P x ∧ Q x) := by
  have hratio := hevent
  rw [uniform_coordinate_eventMass p f P Q h] at hratio
  have hPQ : 0 < Fintype.card {x // P x ∧ Q x} := by
    by_contra hn
    have hz : Fintype.card {x // P x ∧ Q x} = 0 := Nat.eq_zero_of_not_pos hn
    simp [hz] at hratio
  have hP : 0 < Fintype.card {x // P x} := by
    by_contra hn
    have hz : Fintype.card {x // P x} = 0 := Nat.eq_zero_of_not_pos hn
    simp [hz] at hratio
  exact (uniform_coordinate_condition p f P Q h hP hPQ).choose_spec

theorem uniform_coordinate_condition_supported (p : FiniteLaw A) (f : A → X)
    (P Q : X → Prop) (E : A → Prop) (h : UniformCoordinate p f P)
    (heq : ∀ a, p.mass a ≠ 0 → (E a ↔ Q (f a)))
    (hevent : 0 < eventMass p E) :
    UniformCoordinate (condition p E hevent) (fun a => f a.val)
      (fun x => P x ∧ Q x) := by
  have hQ : 0 < eventMass p (fun a => Q (f a)) := by
    rwa [← eventMass_congr_support p E (fun a => Q (f a)) heq]
  have hu := uniform_coordinate_condition_positive p f P Q h hQ
  intro x
  rw [condition_map_mass_congr_support p E (fun a => Q (f a)) heq hevent hQ]
  exact hu x

theorem conditionalCompletionLaw_X_mass
    (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (hm : 0 < m) (α : ℝ) (hα : 0 ≤ α) (hα' : α < 1)
    (x : Fin m → X) :
    ((conditionalCompletionLaw S center output pc po m hm α hα hα').map
      (fun a => a.val.val.1)).mass x =
    ((condition (iidColorLaw S center output pc po m α hα hα'.le)
      (completionEvent S center output m)
      (completionEvent_mass_pos S center output pc po m hm α hα hα')).map
      (fun w i => (w.val i).val.1)).mass x := by
  unfold conditionalCompletionLaw transport
  rw [map_comp_mass]
  rfl

theorem iidColorLaw_allowed
    (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1)
    (w : Fin m → Leaf S)
    (hw : (iidColorLaw S center output pc po m α hα hα').mass w ≠ 0) :
    ∀ i, leafColor S (w i) = center ∨ leafColor S (w i) = output := by
  intro i
  by_contra h
  have hc : leafColor S (w i) ≠ center := fun hc => h (Or.inl hc)
  have ho : leafColor S (w i) ≠ output := fun ho => h (Or.inr ho)
  have hz := colorMix_mass_zero S center output pc po α hα hα' (w i) hc ho
  rw [iidColorLaw, independentProduct_mass] at hw
  exact ((Finset.prod_ne_zero_iff.mp hw) i (Finset.mem_univ i)) hz

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem completionEvent_outputB (S : FlaggedTensor X Y Z) (center : Color)
    (m : ℕ) (w : Fin m → Leaf S)
    (ha : ∀ i, leafColor S (w i) = center ∨ leafColor S (w i) = .B) :
    completionEvent S center .B m w ↔
      (complete S center m).flagB (fun i => (w i).val.1) := by
  have heq : (fun i => leafColor S (w i) = .B) =
      (fun i => S.flagB (w i).val.1) := by
    funext i
    exact propext (leafColor_eq_iff S (w i) .B)
  simp only [completionEvent, ha, forall_true_iff, and_true, heq]
  rfl

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem completionEvent_centerB (S : FlaggedTensor X Y Z) (output : Color)
    (ho : output ≠ .B) (m : ℕ) (w : Fin m → Leaf S)
    (ha : ∀ i, leafColor S (w i) = .B ∨ leafColor S (w i) = output) :
    completionEvent S .B output m w ↔
      ¬ (complete S .B m).flagB (fun i => (w i).val.1) := by
  change (raisedFlag .B output (fun i => leafColor S (w i) = output) ∧ _) ↔
    ¬ raisedFlag .B .B (fun i => S.flagB (w i).val.1)
  simp only [raisedFlag, ite_eq_right ho.symm, ite_true, if_true, ha, forall_true_iff, and_true]
  constructor
  · rintro ⟨i, hi⟩ hall
    have hb := (leafColor_eq_iff S (w i) .B).mpr (hall i)
    exact ho (hi.symm.trans hb)
  · intro hn
    obtain ⟨i, hi⟩ := not_forall.mp hn
    refine ⟨i, (ha i).resolve_left ?_⟩
    exact fun hb => hi ((leafColor_eq_iff S (w i) .B).mp hb)

end MatrixMultiplication.DualUniformConditioning

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_UniformUpdates
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype
attribute [-simp] _root_.OAI.MatrixMultiplication.CompletionTermination.retainedLeafEquiv_coordinates _root_.OAI.MatrixMultiplication.ConditionalLabels.normalizedCountLaw_mass _root_.OAI.MatrixMultiplication.DualInformation.remainingEntropy_zero _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_x _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_y _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_z
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section
universe uCoord
namespace MatrixMultiplication.DualUniformUpdates

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels CompletionColorLaws
open CompletionLaws CompletionProductLaws DualUniformConditioning DualUniformProducts
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

variable {X Y Z : Type uCoord} [Fintype X] [Fintype Y] [Fintype Z]

theorem conditionalCompletionLaw_uniform_independent
    (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (hm : 0 < m) (α : ℝ) (hα : 0 ≤ α) (hα' : α < 1)
    (P : X → Prop)
    (hu : UniformCoordinate (colorMix S center output pc po α hα hα'.le)
      (fun a => a.val.1) P)
    (hi : ∀ x c,
      ((colorMix S center output pc po α hα hα'.le).map
        (fun a => (a.val.1, leafColor S a))).mass (x,c) =
      ((colorMix S center output pc po α hα hα'.le).map (fun a => a.val.1)).mass x *
      ((colorMix S center output pc po α hα hα'.le).map (leafColor S)).mass c) :
    UniformCoordinate
      (conditionalCompletionLaw S center output pc po m hm α hα hα')
      (fun a => a.val.val.1) (fun x => ∀ i, P (x i)) := by
  let p := iidColorLaw S center output pc po m α hα hα'.le
  let f : (Fin m → Leaf S) → (Fin m → X) := fun w i => (w i).val.1
  let g : (Fin m → Leaf S) → (Fin m → Color) := fun w i => leafColor S (w i)
  let Q : (Fin m → Color) → Prop := fun w =>
    raisedFlag center output (fun i => w i = output) ∧
      ∀ i, w i = center ∨ w i = output
  have hprod : UniformCoordinate p f (fun x => ∀ i, P (x i)) :=
    independentProduct_uniformCoordinate
      (fun _ : Fin m => colorMix S center output pc po α hα hα'.le)
      (fun _ a => a.val.1) (fun _ => P) (fun _ => hu)
  have hind : ∀ x c, (p.map (fun a => (f a, g a))).mass (x,c) =
      (p.map f).mass x * (p.map g).mass c :=
    independentProduct_independent
      (fun _ : Fin m => colorMix S center output pc po α hα hα'.le)
      (fun _ a => a.val.1) (fun _ => leafColor S) (fun _ => hi)
  have hcond := uniform_coordinate_independent_condition p f g
    (fun x => ∀ i, P (x i)) Q hprod hind
    (completionEvent_mass_pos S center output pc po m hm α hα hα')
  intro x
  rw [conditionalCompletionLaw_X_mass]
  exact hcond x

theorem conditionalCompletionLaw_uniform_incident
    (S : FlaggedTensor X Y Z) (center output : Color)
    (hc : center = .B ∨ output = .B)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (hm : 0 < m) (α : ℝ) (hα : 0 ≤ α) (hα' : α < 1)
    (hu : UniformCoordinate (colorMix S center output pc po α hα hα'.le)
      (fun a => a.val.1) (fun _ => True)) :
    UniformCoordinate
      (conditionalCompletionLaw S center output pc po m hm α hα hα')
      (fun a => a.val.val.1)
      (fun x => if output = .B then (complete S center m).flagB x
        else ¬ (complete S center m).flagB x) := by
  let p := iidColorLaw S center output pc po m α hα hα'.le
  let f : (Fin m → Leaf S) → (Fin m → X) := fun w i => (w i).val.1
  let Q : (Fin m → X) → Prop := fun x => if output = .B then
    (complete S center m).flagB x else ¬ (complete S center m).flagB x
  have hprod : UniformCoordinate p f (fun _ => True) := by
    apply uniform_coordinate_pred_congr p f (fun x => ∀ _i : Fin m, True)
      (fun _ => True) (fun _ => by simp)
    exact independentProduct_uniformCoordinate
      (fun _ : Fin m => colorMix S center output pc po α hα hα'.le)
      (fun _ a => a.val.1) (fun _ _ => True) (fun _ => hu)
  have heq : ∀ w, p.mass w ≠ 0 →
      (completionEvent S center output m w ↔ Q (f w)) := by
    intro w hw
    have ha := iidColorLaw_allowed S center output pc po m α hα hα'.le w hw
    by_cases ho : output = .B
    · subst output
      simpa only [Q, f, ite_eq_left rfl, ite_true, if_true] using completionEvent_outputB S center m w ha
    · have hcenter : center = .B := hc.resolve_right ho
      subst center
      simpa only [Q, f, ite_eq_right ho] using completionEvent_centerB S output ho m w ha
  have hcond := uniform_coordinate_condition_supported p f (fun _ => True) Q
    (completionEvent S center output m) hprod heq
    (completionEvent_mass_pos S center output pc po m hm α hα hα')
  have hcond' := uniform_coordinate_pred_congr _ _ (fun x => True ∧ Q x) Q
    (fun _ => ⟨And.right, fun h => ⟨True.intro, h⟩⟩) hcond
  intro x
  rw [conditionalCompletionLaw_X_mass]
  exact hcond' x

end MatrixMultiplication.DualUniformUpdates

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_Uniform
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype
attribute [-simp] _root_.OAI.MatrixMultiplication.CompletionTermination.retainedLeafEquiv_coordinates _root_.OAI.MatrixMultiplication.ConditionalLabels.normalizedCountLaw_mass _root_.OAI.MatrixMultiplication.DualInformation.remainingEntropy_zero _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_x _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_y _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_z
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section
universe uCoord
namespace MatrixMultiplication.DualUniform

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels CompletionColorLaws
open CompletionLaws DualCompletionLaws DualUniformConditioning DualUniformUpdates
open DualUniformMixtures CompletionPartitions
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

variable {X Y Z : Type uCoord} [Fintype X] [Fintype Y] [Fintype Z]

theorem UniformLaws.entropy_B (S : FlaggedTensor X Y Z) (p : Laws S)
    (h : UniformLaws S p) :
    finiteEntropy ((p .B).map (fun a => a.val.val.1)).mass = Real.log (activeCount S) :=
  uniform_coordinate_entropy (p .B) _ _ h.B

theorem UniformLaws.entropy_C (S : FlaggedTensor X Y Z) (p : Laws S)
    (h : UniformLaws S p) :
    finiteEntropy ((p .C).map (fun a => a.val.val.1)).mass = Real.log (inactiveCount S) :=
  uniform_coordinate_entropy (p .C) _ _ h.C

theorem conditionalCompletionLaw_uniform_common
    (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (hm : 0 < m) (α : ℝ) (hα : 0 ≤ α) (hα' : α < 1)
    (P : X → Prop)
    (hc : UniformCoordinate pc (fun a => a.val.val.1) P)
    (ho : UniformCoordinate po (fun a => a.val.val.1) P) :
    UniformCoordinate
      (conditionalCompletionLaw S center output pc po m hm α hα hα')
      (fun a => a.val.val.1) (fun x => ∀ i, P (x i)) :=
  conditionalCompletionLaw_uniform_independent S center output pc po m hm α hα hα' P
    (colorMix_uniform_common S center output pc po α hα hα'.le P hc ho)
    (colorMix_independent_uniform S center output pc po α hα hα'.le P hc ho)

private theorem inactive_uniform_update
    (S : FlaggedTensor X Y Z) (center output : Color) (hcenter : center ≠ .B)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (hm : 0 < m) (α : ℝ) (hα : 0 ≤ α) (hα' : α < 1)
    (hc : UniformCoordinate pc (fun a => a.val.val.1) (fun x => ¬ S.flagB x))
    (ho : UniformCoordinate po (fun a => a.val.val.1) (fun x => ¬ S.flagB x)) :
    UniformCoordinate
      (conditionalCompletionLaw S center output pc po m hm α hα hα')
      (fun a => a.val.val.1) (fun x => ¬ (complete S center m).flagB x) := by
  apply uniform_coordinate_pred_congr _ _ (fun x => ∀ i, ¬ S.flagB (x i))
  · intro x
    change (∀ i, ¬ S.flagB (x i)) ↔ ¬ raisedFlag center .B (fun i => S.flagB (x i))
    simp [raisedFlag, hcenter]
  · exact conditionalCompletionLaw_uniform_common S center output pc po m hm α hα hα'
      (fun x => ¬ S.flagB x) hc ho

theorem minusLaws_uniform (S : FlaggedTensor X Y Z) (p : Laws S)
    (m : ℕ) (hm : 0 < m) (rho : ℝ) (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (h : UniformLaws S p) (hrho : rho = activeFraction S) :
    UniformLaws (complete S .B m) (minusLaws S p m hm rho hrho0 hrho1) := by
  constructor
  · exact conditionalCompletionLaw_uniform_common S .B .B (p .B) (p .B) m hm 0
      (by norm_num) (by norm_num) S.flagB h.B h.B
  · have hu := conditionalCompletionLaw_uniform_incident S .B .A (Or.inl rfl)
      (p .B) (p .A) m hm rho hrho0.le hrho1
      (colorMix_uniform_complement S .B .A (p .B) (p .A) rho hrho0.le hrho1.le
        S.flagB h.B h.A hrho)
    simpa only [minusLaws, reduceCtorEq, ite_false, if_false] using hu
  · have hu := conditionalCompletionLaw_uniform_incident S .B .C (Or.inl rfl)
      (p .B) (p .C) m hm rho hrho0.le hrho1
      (colorMix_uniform_complement S .B .C (p .B) (p .C) rho hrho0.le hrho1.le
        S.flagB h.B h.C hrho)
    simpa only [minusLaws, reduceCtorEq, ite_false, if_false] using hu

theorem plusALaws_uniform (S : FlaggedTensor X Y Z) (p : Laws S)
    (m : ℕ) (hm : 0 < m) (rho hA hC : ℝ) (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (h : UniformLaws S p) (hrho : rho = activeFraction S) :
    UniformLaws (complete S .A m) (plusALaws S p m hm rho hA hC hrho0 hrho1) := by
  constructor
  · have hu := conditionalCompletionLaw_uniform_incident S .A .B (Or.inr rfl)
      (p .A) (p .B) m hm (1-rho) (sub_nonneg.mpr hrho1.le) (by linarith)
      (colorMix_uniform_complement_reverse S .A .B (p .A) (p .B) rho
        (sub_nonneg.mpr hrho1.le) (by linarith) S.flagB h.A h.B hrho)
    simpa only [plusALaws, ite_eq_left rfl, ite_true, if_true] using hu
  · exact inactive_uniform_update S .A .A (by intro h; cases h) (p .A) (p .A) m hm 0
      (by norm_num) (by norm_num) h.A h.A
  · exact inactive_uniform_update S .A .C (by intro h; cases h) (p .A) (p .C) m hm
      (gibbsWeight hA hC) (gibbsWeight_nonneg hA hC) (gibbsWeight_lt_one hA hC) h.A h.C

theorem plusCLaws_uniform (S : FlaggedTensor X Y Z) (p : Laws S)
    (m : ℕ) (hm : 0 < m) (rho hA hC : ℝ) (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (h : UniformLaws S p) (hrho : rho = activeFraction S) :
    UniformLaws (complete S .C m) (plusCLaws S p m hm rho hA hC hrho0 hrho1) := by
  constructor
  · have hu := conditionalCompletionLaw_uniform_incident S .C .B (Or.inr rfl)
      (p .C) (p .B) m hm (1-rho) (sub_nonneg.mpr hrho1.le) (by linarith)
      (colorMix_uniform_complement_reverse S .C .B (p .C) (p .B) rho
        (sub_nonneg.mpr hrho1.le) (by linarith) S.flagB h.C h.B hrho)
    simpa only [plusCLaws, ite_eq_left rfl, ite_true, if_true] using hu
  · exact inactive_uniform_update S .C .A (by intro h; cases h) (p .C) (p .A) m hm
      (gibbsWeight hC hA) (gibbsWeight_nonneg hC hA) (gibbsWeight_lt_one hC hA) h.C h.A
  · exact inactive_uniform_update S .C .C (by intro h; cases h) (p .C) (p .C) m hm 0
      (by norm_num) (by norm_num) h.C h.C

private theorem pure_map_mass {A U : Type*} [Fintype A] [Fintype U]
    (a : A) (f : A → U) (x : U) :
    ((FiniteLaw.pure a).map f).mass x = if f a = x then 1 else 0 := by
  rw [FiniteLaw.map_mass, Finset.sum_eq_single a]
  · simp [FiniteLaw.pure]
  · intro b _ hb
    simp [FiniteLaw.pure, hb]
  · simp

theorem baseLaws_uniform : UniformLaws BaseTwo.flagged baseLaws := by
  have hc : Fintype.card {x // BaseTwo.flagged.flagB x} = 1 := by
    exact @Fintype.card_subtype_eq (Fin 2) 1
      (inferInstanceAs (Fintype {x // BaseTwo.flagged.flagB x}))
  constructor <;> intro x <;> rw [baseLaws, pure_map_mass] <;>
    fin_cases x <;>
    norm_num [baseLeaf, BaseTwo.flagged, BaseTwo.flagB, Fintype.card_subtype_compl]
  all_goals rw [hc]

end MatrixMultiplication.DualUniform

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_UniformInstances
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype
attribute [-simp] _root_.OAI.MatrixMultiplication.CompletionTermination.retainedLeafEquiv_coordinates _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_x _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_y _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_z
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section
namespace MatrixMultiplication.DualUniform

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels CompletionColorLaws
open CompletionLaws DualCompletionLaws CompletionPartitions
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

attribute [local instance] coord_nonempty

theorem base_activeFraction : activeFraction BaseTwo.flagged = (1/2 : ℝ) := by
  have hc : activeCount BaseTwo.flagged = 1 :=
    @Fintype.card_subtype_eq (Fin 2) 1
      (inferInstanceAs (Fintype {x // BaseTwo.flagged.flagB x}))
  rw [activeFraction, hc]
  norm_num

theorem rho2 : activeFraction (Script.tensor BaseTwo.flagged script2) =
    DualWitness.state2.rho := by
  change activeFraction (complete BaseTwo.flagged .B 2) = _
  rw [activeFraction_minus, base_activeFraction]
  rfl

theorem rho4 : activeFraction (Script.tensor BaseTwo.flagged script4) =
    DualWitness.state4.rho := by
  change activeFraction (complete (Script.tensor BaseTwo.flagged script2) .A 2) = _
  rw [activeFraction_plus _ .A (by intro h; cases h), rho2]
  rfl

theorem rho8 : activeFraction (Script.tensor BaseTwo.flagged script8) =
    DualWitness.state8.rho := by
  change activeFraction (complete (Script.tensor BaseTwo.flagged script4) .C 2) = _
  rw [activeFraction_plus _ .C (by intro h; cases h), rho4]
  rfl

theorem rho24 : activeFraction (Script.tensor BaseTwo.flagged script24) =
    DualWitness.state24.rho := by
  change activeFraction (complete (Script.tensor BaseTwo.flagged script8) .B 3) = _
  rw [activeFraction_minus, rho8]
  rfl

theorem rho48 : activeFraction (Script.tensor BaseTwo.flagged script48) =
    DualWitness.state48.rho := by
  change activeFraction (complete (Script.tensor BaseTwo.flagged script24) .C 2) = _
  rw [activeFraction_plus _ .C (by intro h; cases h), rho24]
  rfl

theorem rho96 : activeFraction (Script.tensor BaseTwo.flagged script96) =
    DualWitness.state96.rho := by
  change activeFraction (complete (Script.tensor BaseTwo.flagged script48) .B 2) = _
  rw [activeFraction_minus, rho48]
  rfl

theorem rho288 : activeFraction (Script.tensor BaseTwo.flagged Script.dual) =
    DualWitness.state288.rho := by
  change activeFraction (complete (Script.tensor BaseTwo.flagged script96) .A 3) = _
  rw [activeFraction_plus _ .A (by intro h; cases h), rho96]
  rfl

theorem laws2_uniform : UniformLaws (Script.tensor BaseTwo.flagged script2) laws2 :=
  minusLaws_uniform BaseTwo.flagged baseLaws 2 (Nat.zero_lt_succ _) (1/2) (by norm_num)
    (by norm_num) baseLaws_uniform base_activeFraction.symm

theorem laws4_uniform : UniformLaws (Script.tensor BaseTwo.flagged script4) laws4 :=
  plusALaws_uniform _ laws2 2 (Nat.zero_lt_succ _)
    DualWitness.state2.rho DualWitness.state2.hA DualWitness.state2.hC
    (by norm_num [DualWitness.state2, DualWitness.initial, DualWitness.minus])
    (by norm_num [DualWitness.state2, DualWitness.initial, DualWitness.minus])
    laws2_uniform rho2.symm

theorem laws8_uniform : UniformLaws (Script.tensor BaseTwo.flagged script8) laws8 :=
  plusCLaws_uniform _ laws4 2 (Nat.zero_lt_succ _)
    DualWitness.state4.rho DualWitness.state4.hA DualWitness.state4.hC
    (by norm_num [DualWitness.state4, DualWitness.state2, DualWitness.initial,
      DualWitness.minus, DualWitness.plusA])
    (by norm_num [DualWitness.state4, DualWitness.state2, DualWitness.initial,
      DualWitness.minus, DualWitness.plusA]) laws4_uniform rho4.symm

theorem laws24_uniform : UniformLaws (Script.tensor BaseTwo.flagged script24) laws24 :=
  minusLaws_uniform _ laws8 3 (Nat.zero_lt_succ _) DualWitness.state8.rho
    (by rw [DualWitness.state8_rho]; exact DualWitness.rho8_range.1)
    (by rw [DualWitness.state8_rho]; exact DualWitness.rho8_range.2)
    laws8_uniform rho8.symm

theorem laws48_uniform : UniformLaws (Script.tensor BaseTwo.flagged script48) laws48 :=
  plusCLaws_uniform _ laws24 2 (Nat.zero_lt_succ _)
    DualWitness.state24.rho DualWitness.state24.hA DualWitness.state24.hC
    (by rw [DualWitness.state24_rho]; exact DualWitness.rho24_range.1)
    (by rw [DualWitness.state24_rho]; exact DualWitness.rho24_range.2)
    laws24_uniform rho24.symm

theorem laws96_uniform : UniformLaws (Script.tensor BaseTwo.flagged script96) laws96 :=
  minusLaws_uniform _ laws48 2 (Nat.zero_lt_succ _) DualWitness.state48.rho
    (by rw [DualWitness.state48_rho]; exact DualWitness.rho48_range.1)
    (by rw [DualWitness.state48_rho]; exact DualWitness.rho48_range.2)
    laws48_uniform rho48.symm

theorem laws288_uniform : UniformLaws (Script.tensor BaseTwo.flagged Script.dual) laws288 :=
  plusALaws_uniform _ laws96 3 (Nat.zero_lt_succ _)
    DualWitness.state96.rho DualWitness.state96.hA DualWitness.state96.hC
    (by rw [DualWitness.state96_rho]; exact DualWitness.rho96_range.1)
    (by rw [DualWitness.state96_rho]; exact DualWitness.rho96_range.2)
    laws96_uniform rho96.symm

end MatrixMultiplication.DualUniform

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_ScriptIndependence
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.labelRecordZero_subsingleton
attribute [-simp] _root_.OAI.MatrixMultiplication.CW75ReorderedExecution.pairingProduct_zero _root_.OAI.MatrixMultiplication.CompletionExecution.pairingProduct_zero _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_auxiliaryRank _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_columns _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_inner _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_multiplicity _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_occurrences _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_rows _root_.OAI.MatrixMultiplication.CompletionTermination.retainedLeafEquiv_coordinates _root_.OAI.MatrixMultiplication.ConditionalLabels.normalizedCountLaw_mass _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_inner _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_multiplicity _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_outer _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_rank _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_x _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_y _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_z _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.appendCode_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.appendPrefix_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.decodedFine_eq_geometryDecode _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.encodeSourceWord_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.finePrefix_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.mem_conditionalFinset _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.oldPrefix_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.rootPrefixWord_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourcePrefixEquiv_apply_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourcePrefixEquiv_symm_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourceSymbol_encodeSourceWord _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourceSymbol_record
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualProgramIndependence

universe u w

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels
open CompletionColorLaws DualCompletionLaws DualInformation TopologicalFlatten DualUniform

attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

variable {X Y Z : Type u} {Code : Type w} [Fintype X] [Fintype Y] [Fintype Z]
  [Fintype Code] [Inhabited Code] {depth m : ℕ}

theorem minusLaws_independent (S : FlaggedTensor X Y Z) (r : ReadableTensor S)
    (p : Laws S) (m : ℕ) (hm : 0 < m) (rho : ℝ)
    (hrho0 : 0 < rho) (hrho1 : rho < 1) (h : ProgramLawsIndependent S r p) :
    ProgramLawsIndependent (complete S .B m) (ReadableTensor.raise S r .B m)
      (minusLaws S p m hm rho hrho0 hrho1) := by
  intro c n hn
  cases c
  · exact conditionalCompletionLaw_program_factorization S r.program r.context_eq r.view_eq
      .B .B (p .B) (p .B) 0 (le_refl 0) zero_lt_one (Or.inr rfl) hm
      (by intro hh; simp [ownerPair] at hh) (h .B) (h .B) n hn
  · exact conditionalCompletionLaw_program_factorization S r.program r.context_eq r.view_eq
      .B .A (p .B) (p .A) rho hrho0.le hrho1 (Or.inl (by intro he; cases he)) hm
      (by intro hh; simp [ownerPair] at hh) (h .B) (h .A) n hn
  · exact conditionalCompletionLaw_program_factorization S r.program r.context_eq r.view_eq
      .B .C (p .B) (p .C) rho hrho0.le hrho1 (Or.inl (by intro he; cases he)) hm
      (by intro hh; simp [ownerPair] at hh) (h .B) (h .C) n hn

theorem plusALaws_independent (S : FlaggedTensor X Y Z) (r : ReadableTensor S)
    (p : Laws S) (m : ℕ) (hm : 0 < m) (rho hA hC : ℝ)
    (hrho0 : 0 < rho) (hrho1 : rho < 1) (h : ProgramLawsIndependent S r p)
    (hu : UniformLaws S p) :
    ProgramLawsIndependent (complete S .A m) (ReadableTensor.raise S r .A m)
      (plusALaws S p m hm rho hA hC hrho0 hrho1) := by
  intro c n hn
  cases c
  · exact conditionalCompletionLaw_program_factorization S r.program r.context_eq r.view_eq
      .A .B (p .A) (p .B) (1-rho) (sub_nonneg.mpr hrho1.le) (sub_lt_self 1 hrho0)
      (Or.inl (by intro he; cases he)) hm (by intro hh; simp [ownerPair] at hh) (h .A) (h .B) n hn
  · exact conditionalCompletionLaw_program_factorization S r.program r.context_eq r.view_eq
      .A .A (p .A) (p .A) 0 (le_refl 0) zero_lt_one (Or.inr rfl) hm
      (by intro hh; simp [ownerPair] at hh) (h .A) (h .A) n hn
  · exact conditionalCompletionLaw_program_factorization S r.program r.context_eq r.view_eq
      .A .C (p .A) (p .C) (gibbsWeight hA hC)
      (gibbsWeight_nonneg hA hC) (gibbsWeight_lt_one hA hC) (Or.inl (by intro he; cases he)) hm
      (fun _ x => (hu.A x).trans (hu.C x).symm) (h .A) (h .C) n hn

theorem plusCLaws_independent (S : FlaggedTensor X Y Z) (r : ReadableTensor S)
    (p : Laws S) (m : ℕ) (hm : 0 < m) (rho hA hC : ℝ)
    (hrho0 : 0 < rho) (hrho1 : rho < 1) (h : ProgramLawsIndependent S r p)
    (hu : UniformLaws S p) :
    ProgramLawsIndependent (complete S .C m) (ReadableTensor.raise S r .C m)
      (plusCLaws S p m hm rho hA hC hrho0 hrho1) := by
  intro c n hn
  cases c
  · exact conditionalCompletionLaw_program_factorization S r.program r.context_eq r.view_eq
      .C .B (p .C) (p .B) (1-rho) (sub_nonneg.mpr hrho1.le) (sub_lt_self 1 hrho0)
      (Or.inl (by intro he; cases he)) hm (by intro hh; simp [ownerPair] at hh) (h .C) (h .B) n hn
  · exact conditionalCompletionLaw_program_factorization S r.program r.context_eq r.view_eq
      .C .A (p .C) (p .A) (gibbsWeight hC hA)
      (gibbsWeight_nonneg hC hA) (gibbsWeight_lt_one hC hA) (Or.inl (by intro he; cases he)) hm
      (fun _ x => (hu.C x).trans (hu.A x).symm) (h .C) (h .A) n hn
  · exact conditionalCompletionLaw_program_factorization S r.program r.context_eq r.view_eq
      .C .C (p .C) (p .C) 0 (le_refl 0) zero_lt_one (Or.inr rfl) hm
      (by intro hh; simp [ownerPair] at hh) (h .C) (h .C) n hn

theorem base_independent : ProgramLawsIndependent BaseTwo.flagged
    BaseConditionalReaders.baseTwoReadable baseLaws := by
  intro c n
  exact Fin.elim0 n

theorem laws2_independent : ProgramLawsIndependent (Script.tensor BaseTwo.flagged script2)
    (dualReadable script2) laws2 :=
  minusLaws_independent _ _ _ _ _ _ _ _ base_independent

theorem laws4_independent : ProgramLawsIndependent (Script.tensor BaseTwo.flagged script4)
    (dualReadable script4) laws4 :=
  plusALaws_independent _ _ _ _ _ _ _ _ _ _ laws2_independent laws2_uniform

theorem laws8_independent : ProgramLawsIndependent (Script.tensor BaseTwo.flagged script8)
    (dualReadable script8) laws8 :=
  plusCLaws_independent _ _ _ _ _ _ _ _ _ _ laws4_independent laws4_uniform

theorem laws24_independent : ProgramLawsIndependent (Script.tensor BaseTwo.flagged script24)
    (dualReadable script24) laws24 :=
  minusLaws_independent _ _ _ _ _ _ _ _ laws8_independent

theorem laws48_independent : ProgramLawsIndependent (Script.tensor BaseTwo.flagged script48)
    (dualReadable script48) laws48 :=
  plusCLaws_independent _ _ _ _ _ _ _ _ _ _ laws24_independent laws24_uniform

theorem laws96_independent : ProgramLawsIndependent (Script.tensor BaseTwo.flagged script96)
    (dualReadable script96) laws96 :=
  minusLaws_independent _ _ _ _ _ _ _ _ laws48_independent

theorem laws288_independent : ProgramLawsIndependent (Script.tensor BaseTwo.flagged Script.dual)
    (dualReadable Script.dual) laws288 :=
  plusALaws_independent _ _ _ _ _ _ _ _ _ _ laws96_independent laws96_uniform

end MatrixMultiplication.DualProgramIndependence

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_TerminationIndependence
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.labelRecordZero_subsingleton
attribute [-simp] _root_.OAI.MatrixMultiplication.CW75ReorderedExecution.pairingProduct_zero _root_.OAI.MatrixMultiplication.CompletionExecution.pairingProduct_zero _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_auxiliaryRank _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_columns _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_inner _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_multiplicity _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_occurrences _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_rows _root_.OAI.MatrixMultiplication.CompletionTermination.retainedLeafEquiv_coordinates _root_.OAI.MatrixMultiplication.ConditionalLabels.normalizedCountLaw_mass _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_inner _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_multiplicity _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_outer _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_rank _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_x _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_y _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_z _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.appendCode_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.appendPrefix_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.decodedFine_eq_geometryDecode _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.encodeSourceWord_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.finePrefix_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.mem_conditionalFinset _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.oldPrefix_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.rootPrefixWord_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourcePrefixEquiv_apply_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourcePrefixEquiv_symm_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourceSymbol_encodeSourceWord _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourceSymbol_record
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualProgramIndependence

open MatrixMultiplication.Foundation CompletionLabels CompletionLabels.TopologicalFlatten
open CompletionColorLaws DualInformation DualInformationTransport
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

universe u w
variable {X Y Z : Type u} [Fintype X] [Fintype Y] [Fintype Z]
  {Code : Type w} [Fintype Code] [Inhabited Code] {depth : ℕ}

omit [Fintype X] [Fintype Y] [Fintype Z] [Fintype Code] in
theorem termination_label_succ (S : FlaggedTensor X Y Z) (first second : Color)
    (hne : first ≠ second)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (hcontext : ∀ a, p.context a = leafColor S a)
    (hview : ∀ c a, p.view c a = coordinate a.val c)
    (k : ℕ) (a : RetainedLeaf S first second) :
    (terminationProgram S first second hne p hcontext hview).labels (1 + k) a =
      Sum.inr (p.labels k a.val) := by
  exact Program.append_labels_right _ _ _ _ _ k a

omit [Fintype X] [Fintype Y] [Fintype Z] [Fintype Code] in
theorem termination_pair_succ (S : FlaggedTensor X Y Z) (first second : Color)
    (hne : first ≠ second)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (hcontext : ∀ a, p.context a = leafColor S a)
    (hview : ∀ c a, p.view c a = coordinate a.val c) (k : ℕ) :
    (terminationProgram S first second hne p hcontext hview).pair (1 + k) = p.pair k := by
  simp [terminationProgram, Program.append, Program.recode, terminationInherited,
    Program.pullback]

omit [Fintype X] [Fintype Y] [Fintype Z] [Fintype Code] in
theorem termination_record_eq_iff (S : FlaggedTensor X Y Z) (first second : Color)
    (hne : first ≠ second)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (hcontext : ∀ a, p.context a = leafColor S a)
    (hview : ∀ c a, p.view c a = coordinate a.val c)
    (k : ℕ) (a b : RetainedLeaf S first second) :
    labelRecordOf (terminationProgram S first second hne p hcontext hview).labels (1 + k) a =
        labelRecordOf (terminationProgram S first second hne p hcontext hview).labels (1 + k) b ↔
      leafColor S a.val = leafColor S b.val ∧
        labelRecordOf p.labels k a.val = labelRecordOf p.labels k b.val := by
  trans
    (labelRecordOf (terminationRoot S first second hne).labels 1 a =
      labelRecordOf (terminationRoot S first second hne).labels 1 b ∧
      labelRecordOf (terminationInherited S first second p hview).labels k a =
        labelRecordOf (terminationInherited S first second p hview).labels k b)
  · exact (Program.append_record_eq_iff _ _ _ _ _ k a b).trans
      (and_congr
        (Program.recode_record_eq_iff _ _ _ _ 1 a b)
        (Program.recode_record_eq_iff _ _ _ _ k a b))
  simp only [terminationRoot, Program.single, labelRecordOf,
    terminationInherited, Program.pullback]
  have hpull (v : RetainedLeaf S first second) :
      labelRecordOf (fun n (b : RetainedLeaf S first second) => p.labels n b.val) k v =
        labelRecordOf p.labels k v.val := by
    induction k with
    | zero => rfl
    | succ k ih => simp only [labelRecordOf, ih]; rfl
  rw [hpull a, hpull b]
  constructor
  · rintro ⟨he, hr⟩
    exact ⟨congrArg Prod.snd he, hr⟩
  · rintro ⟨he, hr⟩
    refine ⟨?_, hr⟩
    rw [he]

theorem termination_factorization (S : FlaggedTensor X Y Z) (r : ReadableTensor S)
    (p : ∀ c, FiniteLaw (ColorSlice S c)) (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1)
    (h : ProgramLawsIndependent S r p) (k : Fin r.depth)
    (hk : r.program.pair k.val = .yz) :
    ConditionalMassFactorization
      (CompletionTerminationLaw.law S .B .C (p .B) (p .C) a ha ha')
      (labelRecordOf (terminationProgram S .B .C (by intro h; cases h)
        r.program r.context_eq r.view_eq).labels (1 + k.val))
      ((terminationProgram S .B .C (by intro h; cases h)
        r.program r.context_eq r.view_eq).labels (1 + k.val))
      (fun w => w.val.val.1) := by
  let μ := CompletionTerminationLaw.law S .B .C (p .B) (p .C) a ha ha'
  let q := colorMix S .B .C (p .B) (p .C) a ha ha'
  let prior := labelRecordOf r.program.labels k.val
  let label := r.program.labels k.val
  let xx : Leaf S → X := fun w => w.val.1
  have hq : ConditionalMassFactorization q (fun w => (leafColor S w, prior w)) label xx :=
    colorMix_factorization S .B .C (by intro h; cases h) (p .B) (p .C) a ha ha'
      prior label xx (h .B k hk) (h .C k hk)
  have hmass : (μ.map Subtype.val).mass = q.mass := by
    funext w
    exact (CompletionTerminationLaw.law_map_mass S .B .C (p .B) (p .C)
      a ha ha' id w).trans (q.map_mass_apply id Function.injective_id w)
  have hmapped : ConditionalMassFactorization (μ.map Subtype.val)
      (fun w => (leafColor S w, prior w)) label xx :=
    (mass_factorization_congr_mass_iff (μ.map Subtype.val) q hmass _ _ _).mpr hq
  have hμ := (mass_factorization_map_iff μ Subtype.val
    (fun w => (leafColor S w, prior w)) label xx).mp hmapped
  apply mass_factorization_of_same_partitions μ
    (fun w => (leafColor S w.val, prior w.val))
    (fun w => label w.val) (fun w => xx w.val)
    (labelRecordOf (terminationProgram S .B .C (by intro h; cases h)
      r.program r.context_eq r.view_eq).labels (1 + k.val))
    ((terminationProgram S .B .C (by intro h; cases h)
      r.program r.context_eq r.view_eq).labels (1 + k.val))
    (fun w => w.val.val.1) ?_ ?_ ?_ hμ
  · intro u v
    simp only [Prod.mk.injEq]
    exact (termination_record_eq_iff S .B .C (by intro h; cases h)
      r.program r.context_eq r.view_eq k.val u v).symm
  · intro u v
    simp only [termination_label_succ, Sum.inr.injEq]
    rfl
  · intro u v
    rfl

theorem termination_independent (S : FlaggedTensor X Y Z) (r : ReadableTensor S)
    (p : ∀ c, FiniteLaw (ColorSlice S c)) (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1)
    (h : ProgramLawsIndependent S r p)
    (n : Fin (1 + r.depth))
    (hn : (terminationProgram S .B .C (by intro h; cases h)
      r.program r.context_eq r.view_eq).pair n.val = .yz) :
    ConditionalIndependent
      (CompletionTerminationLaw.law S .B .C (p .B) (p .C) a ha ha')
      (labelRecordOf (terminationProgram S .B .C (by intro h; cases h)
        r.program r.context_eq r.view_eq).labels n.val)
      ((terminationProgram S .B .C (by intro h; cases h)
        r.program r.context_eq r.view_eq).labels n.val)
      (fun w => w.val.val.1) := by
  rcases n with ⟨n, hnd⟩
  cases n with
  | zero =>
      simp [terminationProgram, Program.append, Program.recode,
        terminationRoot, Program.single, ownerPair] at hn
  | succ k =>
      have hkd : k < r.depth := Nat.lt_of_succ_lt_succ
        (by simpa only [Nat.one_add] using hnd)
      simp only [Fin.val_mk] at hn ⊢
      simp only [Nat.add_comm k 1] at hn
      have hk : r.program.pair k = .yz :=
        (termination_pair_succ S .B .C (by intro h; cases h)
          r.program r.context_eq r.view_eq k).symm.trans hn
      apply conditionalIndependent_of_mass_factorization
      let labels := (terminationProgram S .B .C (by intro h; cases h)
        r.program r.context_eq r.view_eq).labels
      have hf := termination_factorization S r p a ha ha' h ⟨k, hkd⟩ hk
      exact Eq.mp
        (congrArg
          (fun n : ℕ => ConditionalMassFactorization
            (CompletionTerminationLaw.law S .B .C (p .B) (p .C) a ha ha')
            (labelRecordOf labels n) (labels n) (fun w => w.val.val.1))
          (Nat.one_add k))
        hf

end MatrixMultiplication.DualProgramIndependence

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_HiddenCounts
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionLabels.leafFintype _root_.OAI.MatrixMultiplication.CompletionLabels.retainedLeafFintype _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualHiddenRates

open MatrixMultiplication.Foundation RecursiveCompletion CompletionPartitions
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

variable {X Y Z : Type*} [Fintype X]

theorem inactiveCount_minus_real (S : FlaggedTensor X Y Z) (m : ℕ) :
    (inactiveCount (complete S .B m) : ℝ) =
      ((activeCount S : ℝ) + (inactiveCount S : ℝ)) ^ m -
        (activeCount S : ℝ) ^ m := by
  have h := partition_count (complete S .B m)
  rw [activeCount_minus, Fintype.card_fun, Fintype.card_fin,
    ← partition_count S] at h
  have hreal : (activeCount S : ℝ) ^ m +
      (inactiveCount (complete S .B m) : ℝ) =
      ((activeCount S : ℝ) + (inactiveCount S : ℝ)) ^ m := by
    simpa only [Nat.cast_add, Nat.cast_pow] using
      congrArg (fun n : ℕ => (n : ℝ)) h
  linarith

theorem activeCount_plus_real (S : FlaggedTensor X Y Z) (center : Color)
    (hc : center ≠ .B) (m : ℕ) :
    (activeCount (complete S center m) : ℝ) =
      ((inactiveCount S : ℝ) + (activeCount S : ℝ)) ^ m -
        (inactiveCount S : ℝ) ^ m := by
  have h := partition_count (complete S center m)
  rw [inactiveCount_plus S center hc m, Fintype.card_fun,
    Fintype.card_fin, ← partition_count S] at h
  have hreal : (activeCount (complete S center m) : ℝ) +
      (inactiveCount S : ℝ) ^ m =
      ((activeCount S : ℝ) + (inactiveCount S : ℝ)) ^ m := by
    simpa only [Nat.cast_add, Nat.cast_pow] using
      congrArg (fun n : ℕ => (n : ℝ)) h
  rw [add_comm (activeCount S : ℝ) (inactiveCount S : ℝ)] at hreal
  linarith

theorem activeFraction_ratio (S : FlaggedTensor X Y Z) :
    activeFraction S = (activeCount S : ℝ) /
      ((activeCount S : ℝ) + (inactiveCount S : ℝ)) := by
  rw [activeFraction, ← Nat.cast_add, partition_count]

theorem inactiveFraction_ratio [Nonempty X] (S : FlaggedTensor X Y Z) :
    1 - activeFraction S = (inactiveCount S : ℝ) /
      ((inactiveCount S : ℝ) + (activeCount S : ℝ)) := by
  rw [add_comm (inactiveCount S : ℝ) (activeCount S : ℝ),
    ← Nat.cast_add, partition_count]
  have h := fraction_sum S
  unfold inactiveFraction at h
  linarith

theorem counts_pos [Nonempty X] (S : FlaggedTensor X Y Z)
    (h0 : 0 < activeFraction S) (h1 : activeFraction S < 1) :
    0 < (activeCount S : ℝ) ∧ 0 < (inactiveCount S : ℝ) := by
  have hcard : (0 : ℝ) < Fintype.card X :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hi : 0 < inactiveFraction S := by
    linarith [fraction_sum S]
  constructor
  · exact (div_pos_iff_of_pos_right hcard).mp h0
  · exact (div_pos_iff_of_pos_right hcard).mp hi

end MatrixMultiplication.DualHiddenRates

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_LawEntropy
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype
attribute [-simp] _root_.OAI.MatrixMultiplication.CompletionTermination.retainedLeafEquiv_coordinates _root_.OAI.MatrixMultiplication.ConditionalLabels.normalizedCountLaw_mass _root_.OAI.MatrixMultiplication.DualInformation.remainingEntropy_zero _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_x _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_y _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_z
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualLawEntropy

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels CompletionColorLaws
open CompletionProductLaws CompletionLaws
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

universe u
variable {X Y Z : Type u} [Fintype X] [Fintype Y] [Fintype Z]

theorem iid_allowed (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1) (w : Fin m → Leaf S)
    (hw : (iidColorLaw S center output pc po m a ha ha').mass w ≠ 0) (i : Fin m) :
    leafColor S (w i) = center ∨ leafColor S (w i) = output := by
  change (∏ j : Fin m, (colorMix S center output pc po a ha ha').mass (w j)) ≠ 0 at hw
  have hn : (colorMix S center output pc po a ha ha').mass (w i) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hw) i (Finset.mem_univ i)
  by_contra h
  exact hn (colorMix_mass_zero S center output pc po a ha ha' (w i)
    (fun h' => h (Or.inl h')) (fun h' => h (Or.inr h')))

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem not_event_iff_allCenter (S : FlaggedTensor X Y Z) (center output : Color)
    (hne : center ≠ output) (m : ℕ) (w : Fin m → Leaf S)
    (allowed : ∀ i, leafColor S (w i) = center ∨ leafColor S (w i) = output) :
    ¬ completionEvent S center output m w ↔ allCenter S center m w := by
  constructor
  · intro h i
    rcases allowed i with hi | hi
    · exact hi
    · exfalso
      apply h
      refine ⟨?_, allowed⟩
      simpa only [raisedFlag, ite_eq_right hne] using Exists.intro i hi
  · intro h he
    have hx : ∃ i, leafColor S (w i) = output := by
      simpa only [raisedFlag, ite_eq_right hne] using he.1
    obtain ⟨i, hi⟩ := hx
    exact hne ((h i).symm.trans hi)

theorem event_sum_congr {A : Type*} [Fintype A] (P Q : A → Prop) (f : A → ℝ)
    (agree : ∀ a, f a ≠ 0 → (P a ↔ Q a)) :
    (∑ a : {a // P a}, f a.val) = ∑ a : {a // Q a}, f a.val := by
  rw [sum_subtype_indicator P f, sum_subtype_indicator Q f]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : f a = 0
  · simp [ha]
  · simp only [agree a ha]

theorem removed_event_mass_eq (S : FlaggedTensor X Y Z) (center output : Color)
    (hne : center ≠ output)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1) :
    eventMass (iidColorLaw S center output pc po m a ha ha')
      (fun w => ¬ completionEvent S center output m w) =
    eventMass (iidColorLaw S center output pc po m a ha ha') (allCenter S center m) := by
  apply event_sum_congr
  intro w hw
  exact not_event_iff_allCenter S center output hne m w
    (iid_allowed S center output pc po m a ha ha' w hw)

theorem removed_event_entropy_eq (S : FlaggedTensor X Y Z) (center output : Color)
    (hne : center ≠ output)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1) :
    (∑ w : {w // ¬ completionEvent S center output m w},
      entropyTerm ((iidColorLaw S center output pc po m a ha ha').mass w.val)) =
    ∑ w : {w // allCenter S center m w},
      entropyTerm ((iidColorLaw S center output pc po m a ha ha').mass w.val) := by
  apply event_sum_congr (fun w => ¬ completionEvent S center output m w)
    (allCenter S center m)
    (fun w => entropyTerm ((iidColorLaw S center output pc po m a ha ha').mass w))
  intro w hw
  have hm : (iidColorLaw S center output pc po m a ha ha').mass w ≠ 0 := by
    intro hm
    simp [hm] at hw
  exact not_event_iff_allCenter S center output hne m w
    (iid_allowed S center output pc po m a ha ha' w hm)

theorem center_word_mass (S : FlaggedTensor X Y Z) (center output : Color)
    (hne : center ≠ output)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1)
    (w : {w : Fin m → Leaf S // allCenter S center m w}) :
    (iidColorLaw S center output pc po m a ha ha').mass w.val =
      a ^ m * (independentProduct (fun _ : Fin m => pc)).mass (centerWordEquiv S center m w) := by
  change (∏ i, (colorMix S center output pc po a ha ha').mass (w.val i)) =
    a ^ m * ∏ i, pc.mass ⟨w.val i, w.property i⟩
  have hslot (i : Fin m) : (colorMix S center output pc po a ha ha').mass (w.val i) =
      a * pc.mass ⟨w.val i, w.property i⟩ :=
    colorMix_center_mass S center output hne pc po a ha ha' ⟨w.val i, w.property i⟩
  simp_rw [hslot]
  rw [Finset.prod_mul_distrib]
  simp

theorem allCenter_mass (S : FlaggedTensor X Y Z) (center output : Color)
    (hne : center ≠ output)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1) :
    eventMass (iidColorLaw S center output pc po m a ha ha') (allCenter S center m) = a ^ m := by
  unfold eventMass
  simp_rw [center_word_mass S center output hne pc po m a ha ha']
  rw [← Finset.mul_sum, (centerWordEquiv S center m).sum_comp,
    (independentProduct (fun _ : Fin m => pc)).total, mul_one]

theorem allCenter_entropy (S : FlaggedTensor X Y Z) (center output : Color)
    (hne : center ≠ output)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1) :
    (∑ w : {w // allCenter S center m w},
      entropyTerm ((iidColorLaw S center output pc po m a ha ha').mass w.val)) =
    entropyTerm (a ^ m) + a ^ m * ((m : ℝ) * finiteEntropy pc.mass) := by
  simp_rw [center_word_mass S center output hne pc po m a ha ha']
  rw [(centerWordEquiv S center m).sum_comp
    (fun w => entropyTerm (a ^ m * (independentProduct (fun _ : Fin m => pc)).mass w))]
  change finiteEntropy (fun w => a ^ m *
    (independentProduct (fun _ : Fin m => pc)).mass w) = _
  rw [entropy_scaled_law, independentProduct_entropy]
  simp

theorem conditionalCompletionLaw_entropy (S : FlaggedTensor X Y Z) (center output : Color)
    (hne : center ≠ output)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (hm : 0 < m) (a : ℝ) (ha : 0 ≤ a) (ha' : a < 1) :
    finiteEntropy (conditionalCompletionLaw S center output pc po m hm a ha ha').mass =
      CompletionEntropyAlgebra.conditionalMixEntropy a m
        (finiteEntropy pc.mass) (finiteEntropy po.mass) := by
  rw [conditionalCompletionLaw, transport_entropy]
  have hmass : eventMass (iidColorLaw S center output pc po m a ha ha'.le)
      (fun w => ¬ completionEvent S center output m w) = a ^ m :=
    (removed_event_mass_eq S center output hne pc po m a ha ha'.le).trans
      (allCenter_mass S center output hne pc po m a ha ha'.le)
  have hremoved :
      (∑ w : {w // ¬ completionEvent S center output m w},
        entropyTerm ((iidColorLaw S center output pc po m a ha ha'.le).mass w.val)) =
      entropyTerm (a ^ m) + a ^ m * ((m : ℝ) * finiteEntropy pc.mass) :=
    (removed_event_entropy_eq S center output hne pc po m a ha ha'.le).trans
      (allCenter_entropy S center output hne pc po m a ha ha'.le)
  rw [condition_entropy_of_removed_event _ _ _ (a ^ m)
    ((m : ℝ) * finiteEntropy pc.mass) hmass hremoved]
  rw [iidColorLaw_entropy S center output hne pc po m a ha ha'.le]
  unfold CompletionEntropyAlgebra.conditionalMixEntropy CompletionEntropyAlgebra.binaryEntropy
  congr 1
  ring

end MatrixMultiplication.DualLawEntropy

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_HiddenRates
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualHiddenRates

universe u

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels CompletionColorLaws
open DualCompletionLaws CompletionPartitions CompletionEntropyAlgebra
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

variable {X Y Z : Type u} [Fintype X] [Fintype Y] [Fintype Z]

variable [Nonempty X]

private theorem incident_minus_entropy (S : FlaggedTensor X Y Z) (output : Color)
    (hne : Color.B ≠ output)
    (pc : FiniteLaw (ColorSlice S .B)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (hm : 0 < m) (rho hb ho : ℝ) (h0 : 0 < rho) (h1 : rho < 1)
    (hrho : rho = activeFraction S)
    (hpc : finiteEntropy pc.mass = Real.log (activeCount S) + hb)
    (hpo : finiteEntropy po.mass = Real.log (inactiveCount S) + ho) :
    finiteEntropy (conditionalCompletionLaw S .B output pc po m hm rho h0.le h1).mass =
      Real.log (inactiveCount (complete S .B m)) +
        m * ((rho - rho ^ m) / (1 - rho ^ m) * hb +
          (1 - rho) / (1 - rho ^ m) * ho) := by
  have hc := counts_pos S (hrho ▸ h0) (hrho ▸ h1)
  have hr : (activeCount S : ℝ) / ((activeCount S : ℝ) + inactiveCount S) = rho :=
    (activeFraction_ratio S).symm.trans hrho.symm
  have he := conditionalMixEntropy_incident (activeCount S) (inactiveCount S)
    hb ho m hc.1 hc.2 hm
  dsimp only at he
  rw [hr] at he
  rw [DualLawEntropy.conditionalCompletionLaw_entropy S .B output hne,
    hpc, hpo, inactiveCount_minus_real]
  linarith only [he]

private theorem incident_plus_entropy (S : FlaggedTensor X Y Z) (center : Color)
    (hc : center ≠ .B)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S .B))
    (m : ℕ) (hm : 0 < m) (rho hcEntropy hb : ℝ) (h0 : 0 < rho) (h1 : rho < 1)
    (hrho : rho = activeFraction S)
    (hpc : finiteEntropy pc.mass = Real.log (inactiveCount S) + hcEntropy)
    (hpo : finiteEntropy po.mass = Real.log (activeCount S) + hb) :
    finiteEntropy (conditionalCompletionLaw S center .B pc po m hm (1 - rho)
      (sub_nonneg.mpr h1.le) (by linarith)).mass =
      Real.log (activeCount (complete S center m)) +
        m * (rho / (1 - (1 - rho) ^ m) * hb +
          ((1 - (1 - rho) ^ m) - rho) / (1 - (1 - rho) ^ m) * hcEntropy) := by
  have hcounts := counts_pos S (hrho ▸ h0) (hrho ▸ h1)
  have hr : (inactiveCount S : ℝ) / ((inactiveCount S : ℝ) + activeCount S) =
      1 - rho := by rw [← inactiveFraction_ratio S, ← hrho]
  have he := conditionalMixEntropy_incident (inactiveCount S) (activeCount S)
    hcEntropy hb m hcounts.2 hcounts.1 hm
  dsimp only at he
  rw [hr] at he
  have hcoeff :
      (m : ℝ) * (((1 - rho) - (1 - rho) ^ m) / (1 - (1 - rho) ^ m) * hcEntropy +
        (1 - (1 - rho)) / (1 - (1 - rho) ^ m) * hb) =
      m * (rho / (1 - (1 - rho) ^ m) * hb +
        ((1 - (1 - rho) ^ m) - rho) / (1 - (1 - rho) ^ m) * hcEntropy) := by ring
  rw [hcoeff] at he
  rw [DualLawEntropy.conditionalCompletionLaw_entropy S center .B hc,
    hpc, hpo, activeCount_plus_real S center hc]
  linarith only [he]

omit [Nonempty X] in
private theorem gibbs_entropy (S : FlaggedTensor X Y Z) (center output : Color)
    (hc : center ≠ .B) (hne : center ≠ output)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (hm : 0 < m) (hcEntropy hoEntropy : ℝ)
    (hpc : finiteEntropy pc.mass = Real.log (inactiveCount S) + hcEntropy)
    (hpo : finiteEntropy po.mass = Real.log (inactiveCount S) + hoEntropy) :
    finiteEntropy (conditionalCompletionLaw S center output pc po m hm
      (gibbsWeight hcEntropy hoEntropy) (gibbsWeight_nonneg _ _)
      (gibbsWeight_lt_one _ _)).mass =
      Real.log (inactiveCount (complete S center m)) +
        Real.log ((Real.exp hcEntropy + Real.exp hoEntropy) ^ m -
          Real.exp ((m : ℝ) * hcEntropy)) := by
  rw [DualLawEntropy.conditionalCompletionLaw_entropy S center output hne,
    hpc, hpo, inactiveCount_plus S center hc, Nat.cast_pow, Real.log_pow]
  have he := conditionalMixEntropy_gibbs (inactiveCount S) hcEntropy hoEntropy m hm
  dsimp only [gibbsWeight]
  linarith only [he]

theorem minus_hidden (S : FlaggedTensor X Y Z) (p : Laws S) (s : DualWitness.State)
    (m : ℕ) (hm : 0 < m) (h0 : 0 < s.rho) (h1 : s.rho < 1)
    (hrho : s.rho = activeFraction S) (h : HiddenInvariant S p s) :
    HiddenInvariant (complete S .B m) (minusLaws S p m hm s.rho h0 h1)
      (DualWitness.minus m s) := by
  constructor
  · dsimp only [minusLaws, DualWitness.minus]
    rw [conditionalCompletionLaw_same_zero_entropy, h.B,
      activeCount_minus, Nat.cast_pow, Real.log_pow]
    ring
  · exact incident_minus_entropy S .A (by intro hne; cases hne) (p .B) (p .A) m hm
      s.rho s.hB s.hA h0 h1 hrho h.B h.A
  · exact incident_minus_entropy S .C (by intro hne; cases hne) (p .B) (p .C) m hm
      s.rho s.hB s.hC h0 h1 hrho h.B h.C

theorem plusA_hidden (S : FlaggedTensor X Y Z) (p : Laws S) (s : DualWitness.State)
    (m : ℕ) (hm : 0 < m) (h0 : 0 < s.rho) (h1 : s.rho < 1)
    (hrho : s.rho = activeFraction S) (h : HiddenInvariant S p s) :
    HiddenInvariant (complete S .A m)
      (plusALaws S p m hm s.rho s.hA s.hC h0 h1) (DualWitness.plusA m s) := by
  constructor
  · exact incident_plus_entropy S .A (by intro hne; cases hne) (p .A) (p .B) m hm
      s.rho s.hA s.hB h0 h1 hrho h.A h.B
  · dsimp only [plusALaws, DualWitness.plusA]
    rw [conditionalCompletionLaw_same_zero_entropy, h.A,
      inactiveCount_plus S .A (by intro hne; cases hne), Nat.cast_pow, Real.log_pow]
    ring
  · exact gibbs_entropy S .A .C (by intro hne; cases hne) (by intro hne; cases hne) (p .A) (p .C) m hm
      s.hA s.hC h.A h.C

theorem plusC_hidden (S : FlaggedTensor X Y Z) (p : Laws S) (s : DualWitness.State)
    (m : ℕ) (hm : 0 < m) (h0 : 0 < s.rho) (h1 : s.rho < 1)
    (hrho : s.rho = activeFraction S) (h : HiddenInvariant S p s) :
    HiddenInvariant (complete S .C m)
      (plusCLaws S p m hm s.rho s.hA s.hC h0 h1) (DualWitness.plusC m s) := by
  constructor
  · exact incident_plus_entropy S .C (by intro hne; cases hne) (p .C) (p .B) m hm
      s.rho s.hC s.hB h0 h1 hrho h.C h.B
  · exact gibbs_entropy S .C .A (by intro hne; cases hne) (by intro hne; cases hne) (p .C) (p .A) m hm
      s.hC s.hA h.C h.A
  · dsimp only [plusCLaws, DualWitness.plusC]
    rw [conditionalCompletionLaw_same_zero_entropy, h.C,
      inactiveCount_plus S .C (by intro hne; cases hne), Nat.cast_pow, Real.log_pow]
    ring

end MatrixMultiplication.DualHiddenRates

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_WitnessRecurrence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualWitness

private theorem massA_eq_massC (s : State) :
    massA s = massC s + (1 - s.rho) * (s.hA - s.hC) := by
  dsimp [massA, massC]
  ring

private theorem massC_eq_massA (s : State) :
    massC s = massA s + (1 - s.rho) * (s.hC - s.hA) := by
  dsimp [massA, massC]
  ring

private theorem minus_massA (m : ℕ) (s : State) (h : 1 - s.rho ^ m ≠ 0) :
    massA (minus m s) = m * massA s := by
  dsimp [massA, minus]
  field_simp
  ring

private theorem minus_massC (m : ℕ) (s : State) (h : 1 - s.rho ^ m ≠ 0) :
    massC (minus m s) = m * massC s := by
  dsimp [massC, minus]
  field_simp
  ring

private theorem minus_gap (m : ℕ) (s : State) :
    (minus m s).hC - (minus m s).hA =
      m * ((1 - s.rho) / (1 - s.rho ^ m)) * (s.hC - s.hA) := by
  dsimp [minus]
  ring

private theorem minus_gap_reverse (m : ℕ) (s : State) :
    (minus m s).hA - (minus m s).hC =
      m * ((1 - s.rho) / (1 - s.rho ^ m)) * (s.hA - s.hC) := by
  dsimp [minus]
  ring

private theorem plusA_massA (m : ℕ) (s : State)
    (h : 1 - (1 - s.rho) ^ m ≠ 0) :
    massA (plusA m s) = m * massA s := by
  dsimp [massA, plusA]
  field_simp
  ring

private theorem plusC_massC (m : ℕ) (s : State)
    (h : 1 - (1 - s.rho) ^ m ≠ 0) :
    massC (plusC m s) = m * massC s := by
  dsimp [massC, plusC]
  field_simp
  ring

private theorem log_exp_sum_pow_sub (a c : ℝ) (m : ℕ) (hm : m ≠ 0) :
    Real.log ((Real.exp a + Real.exp c) ^ m - Real.exp ((m : ℝ) * a)) =
      (m : ℝ) * a + Real.log ((1 + Real.exp (c - a)) ^ m - 1) := by
  have h : (1 + Real.exp (c - a)) ^ m - 1 ≠ 0 :=
    (sub_pos.mpr (one_lt_pow₀ (by linarith [Real.exp_pos (c - a)]) hm)).ne'
  have hfactor : Real.exp a + Real.exp c =
      Real.exp a * (1 + Real.exp (c - a)) := by
    rw [mul_add, mul_one, ← Real.exp_add, show a + (c - a) = c by ring]
  have harg : (Real.exp a + Real.exp c) ^ m - Real.exp ((m : ℝ) * a) =
      Real.exp ((m : ℝ) * a) * ((1 + Real.exp (c - a)) ^ m - 1) := by
    rw [hfactor, mul_pow, Real.exp_nat_mul a m]
    ring
  rw [harg, Real.log_mul (Real.exp_ne_zero _) h, Real.log_exp]

theorem state4_hB : state4.hB = 0 := by
  norm_num [state4, state2, initial, minus, plusA]

theorem state4_hA : state4.hA = 0 := by
  norm_num [state4, state2, initial, minus, plusA]

theorem state4_hC : state4.hC = Real.log 3 := by
  norm_num [state4, state2, initial, minus, plusA]

theorem state8_hB : state8.hB = (18 / 25 : ℝ) * Real.log 3 := by
  simp only [state8, plusC, state4_hB, state4_hC]
  norm_num [state4, state2, initial, minus, plusA]
  ring

theorem state8_hA : state8.hA = Real.log 7 := by
  simp only [state8, plusC, state4_hC, state4_hA]
  have he2 := Real.exp_nat_mul (Real.log 3) 2
  norm_num [Real.exp_log (by norm_num : (0 : ℝ) < 3)] at he2
  norm_num [he2, Real.exp_log (by norm_num : (0 : ℝ) < 3)]

theorem state8_hC : state8.hC = 2 * Real.log 3 := by
  simp [state8, plusC, state4_hC]

theorem state8_gap : state8.hC - state8.hA = Real.log (9 / 7 : ℝ) := by
  rw [state8_hC, state8_hA, Real.log_div (by norm_num : (9 : ℝ) ≠ 0)
    (by norm_num : (7 : ℝ) ≠ 0)]
  have h9 : Real.log (9 : ℝ) = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [h9]

theorem state24_gap : state24.hC - state24.hA = delta24 := by
  rw [state24, minus_gap, state8_rho, state8_gap]
  dsimp [delta24, rho24]
  norm_num
  ring

theorem state48_gap : state48.hA - state48.hC = z48 := by
  change Real.log ((Real.exp state24.hC + Real.exp state24.hA) ^ 2 -
    Real.exp (2 * state24.hC)) - 2 * state24.hC = z48
  have hlog := log_exp_sum_pow_sub state24.hC state24.hA 2 (by norm_num)
  simp only [Nat.cast_ofNat] at hlog
  rw [hlog]
  have hgap : state24.hA - state24.hC = -delta24 := by
    linarith [state24_gap]
  rw [hgap]
  dsimp [z48]
  ring

theorem state96_gap : state96.hA - state96.hC = delta96 := by
  rw [state96, minus_gap_reverse, state48_rho, state48_gap]
  norm_num [delta96, rho48, rho24, rho8]
  ring

theorem state288_gap : state288.hC - state288.hA = z288 := by
  change Real.log ((Real.exp state96.hA + Real.exp state96.hC) ^ 3 -
    Real.exp (3 * state96.hA)) - 3 * state96.hA = z288
  have hlog := log_exp_sum_pow_sub state96.hA state96.hC 3 (by norm_num)
  simp only [Nat.cast_ofNat] at hlog
  rw [hlog]
  have hgap : state96.hC - state96.hA = -delta96 := by
    linarith [state96_gap]
  rw [hgap]
  dsimp [z288]
  ring

theorem state288_max : max state288.hA state288.hC = state288.hC := by
  apply max_eq_right
  linarith [state288_gap, ComplexCertificates.z288_bounds.1]

private theorem state8_mass : massC state8 = (9 / 8 : ℝ) * Real.log 3 := by
  dsimp [massC]
  rw [state8_rho, state8_hB, state8_hC]
  norm_num [rho8]
  ring

private theorem state24_mass : massC state24 = 3 * massC state8 := by
  apply minus_massC
  rw [state8_rho]
  exact ne_of_gt (sub_pos.mpr rho24_range.2)

private theorem state48_mass :
    massA state48 = 2 * massC state24 + (1 - rho48) * z48 := by
  rw [massA_eq_massC, state48_gap, state48_rho]
  congr 1
  apply plusC_massC
  rw [state24_rho]
  exact ne_of_gt rho48_range.1

private theorem state96_mass : massA state96 = 2 * massA state48 := by
  apply minus_massA
  rw [state48_rho]
  exact ne_of_gt (sub_pos.mpr rho96_range.2)

private theorem state288_mass :
    massC state288 = 3 * massA state96 + (1 - rho288) * z288 := by
  rw [massC_eq_massA, state288_gap, state288_rho]
  congr 1
  apply plusA_massA
  rw [state96_rho]
  exact ne_of_gt rho288_range.1

theorem state288_normalizedHidden : normalizedHidden state288 = hiddenRate := by
  rw [normalizedHidden, state288_max, state_factors]
  change massC state288 / 288 = hiddenRate
  rw [state288_mass, state96_mass, state48_mass, state24_mass, state8_mass]
  dsimp [hiddenRate]
  ring

end MatrixMultiplication.DualWitness

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_HiddenInstances
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype
attribute [-simp] _root_.OAI.MatrixMultiplication.CompletionTermination.retainedLeafEquiv_coordinates _root_.OAI.MatrixMultiplication.ConditionalLabels.normalizedCountLaw_mass _root_.OAI.MatrixMultiplication.DualInformation.remainingEntropy_zero _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_x _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_y _root_.OAI.MatrixMultiplication.DualWitnessRealization.hierarchy_z
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualHiddenRates

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels CompletionColorLaws
open CompletionLaws DualCompletionLaws CompletionPartitions
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

private theorem coord_nonempty (s : Script) : Nonempty (Script.Coord (Fin 2) s) := by
  induction s with
  | base => exact inferInstanceAs (Nonempty (Fin 2))
  | step prior center m ih =>
    let := ih
    exact inferInstanceAs (Nonempty (Fin m → Script.Coord (Fin 2) prior))
attribute [local instance] coord_nonempty

theorem base_hidden : HiddenInvariant BaseTwo.flagged baseLaws DualWitness.initial := by
  have hc : Fintype.card {x // BaseTwo.flagged.flagB x} = 1 :=
    @Fintype.card_subtype_eq (Fin 2) 1
      (inferInstanceAs (Fintype {x // BaseTwo.flagged.flagB x}))
  constructor <;>
    norm_num [baseLaws, DualWitness.initial, activeCount, inactiveCount,
      BaseTwo.flagged, BaseTwo.flagB, Fintype.card_subtype_compl]
  all_goals norm_num [hc]

theorem laws2_hidden : HiddenInvariant (Script.tensor BaseTwo.flagged script2)
    laws2 DualWitness.state2 :=
  minus_hidden BaseTwo.flagged baseLaws DualWitness.initial 2 (by norm_num)
    (by norm_num [DualWitness.initial]) (by norm_num [DualWitness.initial])
    DualUniform.base_activeFraction.symm base_hidden

theorem laws4_hidden : HiddenInvariant (Script.tensor BaseTwo.flagged script4)
    laws4 DualWitness.state4 :=
  plusA_hidden _ laws2 DualWitness.state2 2 (by norm_num)
    (by norm_num [DualWitness.state2, DualWitness.initial, DualWitness.minus])
    (by norm_num [DualWitness.state2, DualWitness.initial, DualWitness.minus])
    DualUniform.rho2.symm laws2_hidden

theorem laws8_hidden : HiddenInvariant (Script.tensor BaseTwo.flagged script8)
    laws8 DualWitness.state8 :=
  plusC_hidden _ laws4 DualWitness.state4 2 (by norm_num)
    (by norm_num [DualWitness.state4, DualWitness.state2, DualWitness.initial,
      DualWitness.minus, DualWitness.plusA])
    (by norm_num [DualWitness.state4, DualWitness.state2, DualWitness.initial,
      DualWitness.minus, DualWitness.plusA])
    DualUniform.rho4.symm laws4_hidden

theorem laws24_hidden : HiddenInvariant (Script.tensor BaseTwo.flagged script24)
    laws24 DualWitness.state24 :=
  minus_hidden _ laws8 DualWitness.state8 3 (by norm_num)
    (by rw [DualWitness.state8_rho]; exact DualWitness.rho8_range.1)
    (by rw [DualWitness.state8_rho]; exact DualWitness.rho8_range.2)
    DualUniform.rho8.symm laws8_hidden

theorem laws48_hidden : HiddenInvariant (Script.tensor BaseTwo.flagged script48)
    laws48 DualWitness.state48 :=
  plusC_hidden _ laws24 DualWitness.state24 2 (by norm_num)
    (by rw [DualWitness.state24_rho]; exact DualWitness.rho24_range.1)
    (by rw [DualWitness.state24_rho]; exact DualWitness.rho24_range.2)
    DualUniform.rho24.symm laws24_hidden

theorem laws96_hidden : HiddenInvariant (Script.tensor BaseTwo.flagged script96)
    laws96 DualWitness.state96 :=
  minus_hidden _ laws48 DualWitness.state48 2 (by norm_num)
    (by rw [DualWitness.state48_rho]; exact DualWitness.rho48_range.1)
    (by rw [DualWitness.state48_rho]; exact DualWitness.rho48_range.2)
    DualUniform.rho48.symm laws48_hidden

theorem laws288_hidden : HiddenInvariant (Script.tensor BaseTwo.flagged Script.dual)
    laws288 DualWitness.state288 :=
  plusA_hidden _ laws96 DualWitness.state96 3 (by norm_num)
    (by rw [DualWitness.state96_rho]; exact DualWitness.rho96_range.1)
    (by rw [DualWitness.state96_rho]; exact DualWitness.rho96_range.2)
    DualUniform.rho96.symm laws96_hidden

theorem laws288_hidden_B :
    finiteEntropy (laws288 .B).mass -
      finiteEntropy ((laws288 .B).map (fun a => a.val.val.1)).mass =
        DualWitness.state288.hB := by
  rw [laws288_hidden.B,
    DualUniform.UniformLaws.entropy_B _ _ DualUniform.laws288_uniform]
  ring

theorem laws288_hidden_C :
    finiteEntropy (laws288 .C).mass -
      finiteEntropy ((laws288 .C).map (fun a => a.val.val.1)).mass =
        DualWitness.state288.hC := by
  rw [laws288_hidden.C,
    DualUniform.UniformLaws.entropy_C _ _ DualUniform.laws288_uniform]
  ring

theorem laws288_normalizedHidden :
    (DualWitness.state288.rho * (finiteEntropy (laws288 .B).mass -
      finiteEntropy ((laws288 .B).map (fun a => a.val.val.1)).mass) +
      (1 - DualWitness.state288.rho) * (finiteEntropy (laws288 .C).mass -
        finiteEntropy ((laws288 .C).map (fun a => a.val.val.1)).mass)) / 288 =
      DualWitness.hiddenRate := by
  rw [laws288_hidden_B, laws288_hidden_C]
  have h := DualWitness.state288_normalizedHidden
  rw [DualWitness.normalizedHidden, DualWitness.state288_max,
    DualWitness.state_factors] at h
  exact h

theorem laws288_weightedHidden :
    DualWitness.state288.rho * (finiteEntropy (laws288 .B).mass -
      finiteEntropy ((laws288 .B).map (fun a => a.val.val.1)).mass) +
      (1 - DualWitness.state288.rho) * (finiteEntropy (laws288 .C).mass -
        finiteEntropy ((laws288 .C).map (fun a => a.val.val.1)).mass) =
      288 * DualWitness.hiddenRate := by
  linarith only [laws288_normalizedHidden]

theorem laws288_coordinateEntropy :
    CompletionEntropyAlgebra.binaryEntropy DualWitness.state288.rho +
      DualWitness.state288.rho *
        Real.log (activeCount (Script.tensor BaseTwo.flagged Script.dual)) +
      (1 - DualWitness.state288.rho) *
        Real.log (inactiveCount (Script.tensor BaseTwo.flagged Script.dual)) =
      Real.log (Fintype.card (Script.Coord (Fin 2) Script.dual)) := by
  have hc := counts_pos (Script.tensor BaseTwo.flagged Script.dual)
    (by
      rw [DualUniform.rho288, DualWitness.state288_rho]
      exact DualWitness.rho288_range.1)
    (by
      rw [DualUniform.rho288, DualWitness.state288_rho]
      exact DualWitness.rho288_range.2)
  have h := CompletionEntropyAlgebra.binaryEntropy_cardinal_mixture
    (activeCount (Script.tensor BaseTwo.flagged Script.dual))
    (inactiveCount (Script.tensor BaseTwo.flagged Script.dual)) hc.1 hc.2
  dsimp only at h
  rw [← activeFraction_ratio, DualUniform.rho288, ← Nat.cast_add, partition_count] at h
  exact h

end MatrixMultiplication.DualHiddenRates

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_WitnessProgram
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.labelRecordZero_subsingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualWitness

attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels

theorem program_complete : program.Complete :=
  terminationProgram_complete source .B .C (by intro h; cases h)
    readable.program readable.context_eq readable.view_eq readable.complete

theorem record_injective : Function.Injective
    (labelRecordOf program.labels (1 + readable.depth)) :=
  terminationRecord_injective source .B .C (by intro h; cases h)
    readable.program readable.context_eq readable.view_eq readable.complete

theorem coord_card (U : Type*) [Fintype U] (s : Script) :
    Fintype.card (Script.Coord U s) = Fintype.card U ^ s.factors := by
  induction s with
  | base =>
    change Fintype.card U = Fintype.card U ^ 1
    exact (pow_one _).symm
  | step prior center m ih =>
    change Fintype.card (Fin m → Script.Coord U prior) = _
    simp only [Fintype.card_fun, Fintype.card_fin, ih, Script.factors, pow_mul]

theorem word_card : Fintype.card Word = 2 ^ 288 := by
  simpa only [Fintype.card_fin, Script.dual_factors] using coord_card (Fin 2) Script.dual

end MatrixMultiplication.DualWitness

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_Witness
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualWitness

attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels
open CompletionLaws CompletionColorLaws DualCompletionLaws

theorem law_uniform : UniformCoordinate law x (fun _ => True) := by
  have hu := DualUniformMixtures.colorMix_uniform_complement source .B .C
    (laws288 .B) (laws288 .C) state288.rho
    (by rw [state288_rho]; exact rho288_range.1.le)
    (by rw [state288_rho]; exact rho288_range.2.le)
    source.flagB DualUniform.laws288_uniform.B DualUniform.laws288_uniform.C
    DualUniform.rho288.symm
  intro u
  change ((law.map (fun a : Support => a.val.val.1)).mass u) = _
  exact (CompletionTerminationLaw.law_map_mass source .B .C
    (laws288 .B) (laws288 .C) state288.rho
    (by rw [state288_rho]; exact rho288_range.1.le)
    (by rw [state288_rho]; exact rho288_range.2.le)
    (fun a : Leaf source => a.val.1) u).trans (hu u)

theorem x_entropy : finiteEntropy (law.map x).mass = 288 * Real.log 2 := by
  rw [uniform_coordinate_entropy law x (fun _ => True) law_uniform]
  simp only [Fintype.card_subtype_true, word_card, Nat.cast_pow, Nat.cast_ofNat,
    Real.log_pow]

theorem rate_sum : rate .xy + rate .xz + rate .yz = finiteEntropy law.mass :=
  ConditionalLabels.lawPairingRate_sum law program.labels (1 + readable.depth)
    (fun n => program.pair n.val) record_injective

end MatrixMultiplication.DualWitness

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_WitnessEntropy
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualWitness

attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels
open CompletionLaws CompletionColorLaws DualCompletionLaws CompletionPartitions

theorem law_entropy : finiteEntropy law.mass =
    288 * Real.log 2 + 288 * hiddenRate := by
  have hhidden := DualHiddenRates.laws288_weightedHidden
  rw [DualUniform.UniformLaws.entropy_B _ _ DualUniform.laws288_uniform,
    DualUniform.UniformLaws.entropy_C _ _ DualUniform.laws288_uniform] at hhidden
  have hcoord := DualHiddenRates.laws288_coordinateEntropy
  change CompletionEntropyAlgebra.binaryEntropy state288.rho +
      state288.rho * Real.log (activeCount source) +
      (1 - state288.rho) * Real.log (inactiveCount source) =
      Real.log (Fintype.card Word) at hcoord
  rw [word_card, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at hcoord
  unfold CompletionEntropyAlgebra.binaryEntropy at hcoord
  dsimp only [source] at hcoord
  norm_num only [Nat.cast_ofNat] at hcoord
  change finiteEntropy (CompletionTerminationLaw.law
      (Script.tensor BaseTwo.flagged Script.dual) .B .C (laws288 .B) (laws288 .C)
      state288.rho _ _).mass = _
  rw [CompletionTerminationLaw.law_entropy _ .B .C (by intro h; cases h)]
  linarith only [hhidden, hcoord]

end MatrixMultiplication.DualWitness

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_WitnessRates
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.labelRecordZero_subsingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualWitnessRates

attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

open MatrixMultiplication.Foundation CompletionLabels CompletionLabels.TopologicalFlatten
open DualInformation DualCompletionLaws DualWitness

theorem nonincident_independent (n : Fin (1 + readable.depth))
    (hn : program.pair n.val = .yz) :
    ConditionalIndependent law (labelRecordOf program.labels n.val)
      (program.labels n.val) x := by
  exact DualProgramIndependence.termination_independent source readable laws288
    state288.rho
    (by rw [state288_rho]; exact rho288_range.1.le)
    (by rw [state288_rho]; exact rho288_range.2.le)
    DualProgramIndependence.laws288_independent n hn

theorem incident_rate : rate .xy + rate .xz = 288 * Real.log 2 := by
  let : Fintype (Coordinate Word Word Word .B) := inferInstanceAs (Fintype Word)
  have h := program.incident_rate_eq_x_entropy law program_complete PUnit.unit
    (fun _ => rfl) (fun n hn => nonincident_independent n hn)
  change rate .xy + rate .xz = finiteEntropy (law.map x).mass at h
  rw [x_entropy] at h
  exact h

theorem hidden_rate : rate .yz = 288 * hiddenRate := by
  linarith only [rate_sum, law_entropy, incident_rate]

end MatrixMultiplication.DualWitnessRates

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_WitnessRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualWitnessRealization

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels
open CompletionLabels.TopologicalFlatten CompletionHierarchyWords
open scoped BigOperators Classical

theorem hierarchy_complete :
    Function.Injective (labelRecordOf hierarchy.labels hierarchy.depth) :=
  ReadableHierarchy.ofProgram_complete DualWitness.program PUnit.unit program_context
    program_joint DualWitness.program_complete

theorem base_unit (x y z : Fin 2) (h : BaseTwo.tensor x y z ≠ 0) :
    BaseTwo.tensor x y z = 1 := by
  unfold BaseTwo.tensor at h ⊢
  split_ifs with hsum
  · rfl
  · simp [hsum] at h

theorem tensor_unit_coefficients (x y z : DualWitness.Word) (h : tensor x y z ≠ 0) :
    tensor x y z = 1 := by
  obtain ⟨hs, ha⟩ := (CompletionTermination.support_iff DualWitness.source .A x y z).mp h
  change (if ownerFlag DualWitness.source .A (coordinate (x, y, z) .A) then 0
    else DualWitness.source.tensor x y z) = 1
  rw [ite_eq_right ha]
  exact CompletionFiniteRealization.script_coefficient_one BaseTwo.flagged base_unit
    Script.dual x y z hs

theorem source_supported (x y z : DualWitness.Word) (h : tensor x y z ≠ 0) :
    ∃ a : DualWitness.Support, hierarchy.x a = x ∧ hierarchy.y a = y ∧ hierarchy.z a = z :=
  ⟨retainedLeafEquiv ⟨(x, y, z), h⟩, rfl, rfl, rfl⟩

theorem source_unit (a : DualWitness.Support) :
    tensor (hierarchy.x a) (hierarchy.y a) (hierarchy.z a) = 1 :=
  tensor_unit_coefficients _ _ _ (retainedLeafEquiv.symm a).property

theorem source_log : Real.log ((2 ^ 288 : ℕ) : ℝ) = 288 * Real.log 2 := by
  rw [Nat.cast_pow, Real.log_pow]
  norm_num

theorem source_log_positive : 0 < Real.log ((2 ^ 288 : ℕ) : ℝ) := by
  rw [source_log]
  exact mul_pos (by norm_num) (Real.log_pos (by norm_num))

end MatrixMultiplication.DualWitnessRealization

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_ExponentBound
attribute [-simp] _root_.OAI.MatrixMultiplication.CW75ReorderedExecution.pairingProduct_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualWitnessRealization

@[simp] theorem pairRate_law (pair : ReaderPair) :
    DualFiniteRealization.pairRate hierarchy DualWitness.law pair = DualWitness.rate pair := rfl

end MatrixMultiplication.DualWitnessRealization

namespace MatrixMultiplication.DualExponentBound

open DualWitnessRealization

theorem fixedAspect_actual_families :
    ∀ ε : ℝ, 0 < ε → Nonempty (ActualFamily fixedAspect (2 + ε)) := by
  apply DualFiniteRealization.arbitrarily_close_families_of_exact_incident
    hierarchy hierarchy_complete DualWitness.law approximation
    (pow_pos (by decide : 0 < (2 : ℕ)) 288) source_supported source_unit
    source_log_positive
  · rw [pairRate_law, pairRate_law, source_log]
    exact DualWitnessRates.incident_rate
  · rw [pairRate_law, pairRate_law, pairRate_law,
      DualWitnessRates.incident_rate, DualWitnessRates.hidden_rate]
    have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hgap := (lt_div_iff₀ hlog).mp fixedAspect_lt_dual_aspect
    change fixedAspect * Real.log 2 < 2 * DualWitness.hiddenRate at hgap
    nlinarith

theorem alpha_gt : (93 : ℝ) / 200 < Arithmetic.complexAlpha :=
  alpha_gt_target_of_arbitrarily_close_families fixedAspect_actual_families

end MatrixMultiplication.DualExponentBound

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arithmetic complexity bounds for square and rectangular matrix multiplication. -/

namespace MatrixMultiplication

/-- The complex dual matrix multiplication exponent is greater than `0.465`. -/
theorem complex_alpha_gt_93_div_200_oai :
    (93 : ℝ) / 200 < Arithmetic.complexAlpha :=
  DualExponentBound.alpha_gt

end MatrixMultiplication

end OAI
end

theorem solution : type_of% @OAI.MatrixMultiplication.complex_alpha_gt_93_div_200_oai := @OAI.MatrixMultiplication.complex_alpha_gt_93_div_200_oai
