-- Prove2me | solution 1 for OAI.MatrixMultiplication.complex_rectangular_omega_lt_523_div_250
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T18:27:08.846647+00:00
-- url     : https://prove2.me/submissions/81bdfde1-c61b-4671-a3a9-ac3258e87e30

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
-- module Solutions.Q235_MM.MatrixMultiplication_Arithmetic_Padding
attribute [-simp] _root_.OAI.MatrixMultiplication.Arithmetic.RecursiveBlock.Family.cost_ofMatrix
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

theorem tendsto_finiteEntropy_of_tendsto {I A : Type*} [Fintype A]
    {l : Filter I} {p : I → A → ℝ} {q : A → ℝ}
    (h : ∀ a, Tendsto (fun i => p i a) l (𝓝 (q a))) :
    Tendsto (fun i => finiteEntropy (p i)) l (𝓝 (finiteEntropy q)) :=
  continuous_finiteEntropy.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr h)

namespace FiniteLaw

variable {A : Type*} [Fintype A]

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
attribute [-simp] _root_.OAI.MatrixMultiplication.CompletionProductLaws.independentProduct_mass _root_.OAI.MatrixMultiplication.CompletionProductLaws.sigmaJoint_mass _root_.OAI.MatrixMultiplication.ConditionalLabels.normalizedCountLaw_mass _root_.OAI.MatrixMultiplication.Foundation.FiniteLabelHierarchy.prefixLaw_succ _root_.OAI.MatrixMultiplication.Foundation.FiniteLabelHierarchy.prefixLaw_succ_mass _root_.OAI.MatrixMultiplication.Foundation.FiniteLabelHierarchy.prefixLaw_zero_mass _root_.OAI.MatrixMultiplication.Foundation.FiniteLaw.uniform_mass
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
-- module Solutions.Q235_MM.MatrixMultiplication_Entropy_ComplexHierarchyEntropy
attribute [-instance] _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.labelRecordZero_subsingleton
attribute [-simp] _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_auxiliaryRank _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_columns _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_inner _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_multiplicity _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_occurrences _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_rows _root_.OAI.MatrixMultiplication.CompletionProductLaws.independentProduct_mass _root_.OAI.MatrixMultiplication.CompletionProductLaws.sigmaJoint_mass _root_.OAI.MatrixMultiplication.ConditionalLabels.normalizedCountLaw_mass _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_inner _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_multiplicity _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_outer _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_rank _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.appendCode_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.appendPrefix_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.decodedFine_eq_geometryDecode _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.encodeSourceWord_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.finePrefix_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.mem_conditionalFinset _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.oldPrefix_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.rootPrefixWord_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourcePrefixEquiv_apply_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourcePrefixEquiv_symm_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourceSymbol_encodeSourceWord _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourceSymbol_record _root_.OAI.MatrixMultiplication.Foundation.FiniteLaw.uniform_mass _root_.OAI.MatrixMultiplication.Foundation.RationalLaw.toFiniteLaw_mass _root_.OAI.MatrixMultiplication.Foundation.entropyTerm_one
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
-- module Solutions.Q235_MM.MatrixMultiplication_Separation_ComplexStageHierarchyResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

noncomputable section

namespace MatrixMultiplication.Foundation.StageHierarchyResources

open Filter HierarchySeparationRates LabelHierarchyCounts
open scoped BigOperators Topology

universe u v

variable {A : Type u} [Fintype A] {Label : ℕ → Type v}
  [∀ n, Fintype (Label n)]

local instance (priority := low) instDecidableEq_solutions_rd27673_1 {B : Type*} : DecidableEq B := Classical.decEq B
theorem stageAuxiliaryBudget_pos (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth t : ℕ) :
    0 < stageAuxiliaryBudget counts labels depth t := by
  exact Finset.prod_pos (fun n _ => LabelHierarchySeparation.poolAuxiliaryCost_pos
    (stageRefinementCount counts labels n.val t))

end MatrixMultiplication.Foundation.StageHierarchyResources

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
-- module Solutions.Q235_MM.MatrixMultiplication_Entropy_ConditionalLabels
attribute [-instance] _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.labelRecordZero_subsingleton
attribute [-simp] _root_.OAI.MatrixMultiplication.CW75ReorderedExecution.pairingProduct_zero _root_.OAI.MatrixMultiplication.CompletionExecution.pairingProduct_zero _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_auxiliaryRank _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_columns _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_inner _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_multiplicity _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_occurrences _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_rows _root_.OAI.MatrixMultiplication.CompletionProductLaws.independentProduct_mass _root_.OAI.MatrixMultiplication.CompletionProductLaws.sigmaJoint_mass _root_.OAI.MatrixMultiplication.ConditionalLabels.normalizedCountLaw_mass _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_inner _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_multiplicity _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_outer _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_rank _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.appendCode_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.appendPrefix_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.decodedFine_eq_geometryDecode _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.encodeSourceWord_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.finePrefix_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.mem_conditionalFinset _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.oldPrefix_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.rootPrefixWord_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourcePrefixEquiv_apply_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourcePrefixEquiv_symm_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourceSymbol_encodeSourceWord _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourceSymbol_record
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

theorem incident_rate_eq_prefix_entropy (p : FiniteLaw A)
    (labels : ∀ n, A → Label n) (depth cut : ℕ) (hcut : cut ≤ depth)
    (reader : Fin depth → ReaderPair)
    (incident_prefix : ∀ n : Fin depth,
      (reader n = .xy ∨ reader n = .xz) ↔ n.val < cut) :
    lawPairingRate p labels depth reader .xy +
      lawPairingRate p labels depth reader .xz =
      finiteEntropy (p.map (labelRecordOf labels cut)).mass := by
  let hierarchy := FiniteLabelHierarchy.ofLawLabels p labels depth
  have hterms : ∀ n : Fin depth,
      (if reader n = .xy then hierarchy.refinementEntropy n.val else 0) +
        (if reader n = .xz then hierarchy.refinementEntropy n.val else 0) =
        if n.val < cut then hierarchy.refinementEntropy n.val else 0 := by
    intro n
    cases hr : reader n with
    | xy =>
        have hn := (incident_prefix n).mp (Or.inl hr)
        simp [hn]
    | xz =>
        have hn := (incident_prefix n).mp (Or.inr hr)
        simp [hn]
    | yz =>
        have hn : ¬n.val < cut := by
          intro h
          rcases (incident_prefix n).mpr h with h | h <;> simp [hr] at h
        simp [hn]
  have hfilter : (Finset.range depth).filter (fun n => n < cut) = Finset.range cut := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  calc
    lawPairingRate p labels depth reader .xy +
        lawPairingRate p labels depth reader .xz =
        ∑ n : Fin depth, if n.val < cut then hierarchy.refinementEntropy n.val else 0 := by
      simp only [lawPairingRate, pairingRate, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun n _ => hterms n)
    _ = ∑ n ∈ Finset.range cut, hierarchy.refinementEntropy n := by
      rw [show (∑ n : Fin depth, if n.val < cut then hierarchy.refinementEntropy n.val else 0) =
        ∑ n ∈ Finset.range depth, if n < cut then hierarchy.refinementEntropy n else 0 from
          Fin.sum_univ_eq_sum_range
            (fun n => if n < cut then hierarchy.refinementEntropy n else 0) depth]
      rw [← Finset.sum_filter, hfilter]
    _ = finiteEntropy (hierarchy.prefixLaw cut hcut).mass :=
      (hierarchy.prefixLaw_entropy cut hcut).symm
    _ = finiteEntropy (p.map (labelRecordOf labels cut)).mass := by
      rw [FiniteLabelHierarchy.ofLawLabels_prefixLaw_mass]

theorem remaining_rate_eq_entropy_sub_prefix (p : FiniteLaw A)
    (labels : ∀ n, A → Label n) (depth cut : ℕ) (hcut : cut ≤ depth)
    (reader : Fin depth → ReaderPair)
    (incident_prefix : ∀ n : Fin depth,
      (reader n = .xy ∨ reader n = .xz) ↔ n.val < cut)
    (complete : Function.Injective (labelRecordOf labels depth)) :
    lawPairingRate p labels depth reader .yz = finiteEntropy p.mass -
      finiteEntropy (p.map (labelRecordOf labels cut)).mass := by
  have hsum := lawPairingRate_sum p labels depth reader complete
  have hprefix := incident_rate_eq_prefix_entropy p labels depth cut hcut reader incident_prefix
  linarith

end SourceHierarchy
end ConditionalLabels
end MatrixMultiplication

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
-- module Solutions.Q235_MM.MatrixMultiplication_Tensor_ComplexWitness
attribute [-instance] _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.labelRecordZero_subsingleton
attribute [-simp] _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_auxiliaryRank _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_columns _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_inner _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_multiplicity _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_occurrences _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_rows _root_.OAI.MatrixMultiplication.CompletionProductLaws.independentProduct_mass _root_.OAI.MatrixMultiplication.CompletionProductLaws.sigmaJoint_mass _root_.OAI.MatrixMultiplication.ConditionalLabels.normalizedCountLaw_mass _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_inner _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_multiplicity _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_outer _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_rank _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.appendCode_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.appendPrefix_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.decodedFine_eq_geometryDecode _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.encodeSourceWord_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.finePrefix_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.mem_conditionalFinset _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.oldPrefix_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.rootPrefixWord_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourcePrefixEquiv_apply_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourcePrefixEquiv_symm_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourceSymbol_encodeSourceWord _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourceSymbol_record
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

noncomputable section

open scoped BigOperators
open Filter

namespace MatrixMultiplication.ComplexWitness

open MatrixMultiplication.Foundation

theorem curve_fiber_histogram :
    (Finset.univ.filter fun u : CurveCoordinate => curveFiberSize u = 1).card = 8 ∧
    (Finset.univ.filter fun u : CurveCoordinate => curveFiberSize u = 2).card = 12 ∧
    (Finset.univ.filter fun u : CurveCoordinate => curveFiberSize u = 4).card = 6 ∧
    (Finset.univ.filter fun u : CurveCoordinate => curveFiberSize u = 19).card = 1 := by
  decide

theorem curve_fiber_values : ∀ u : CurveCoordinate,
    curveFiberSize u = 1 ∨ curveFiberSize u = 2 ∨
      curveFiberSize u = 4 ∨ curveFiberSize u = 19 := by
  decide

theorem sum_curveFiberSizes (f : ℕ → ℝ) :
    (∑ u : CurveCoordinate, f (curveFiberSize u)) =
      8 * f 1 + 12 * f 2 + 6 * f 4 + f 19 := by
  classical
  rcases curve_fiber_histogram with ⟨h1, h2, h4, h19⟩
  have he (u : CurveCoordinate) : f (curveFiberSize u) =
      (if curveFiberSize u = 1 then f 1 else 0) +
      (if curveFiberSize u = 2 then f 2 else 0) +
      (if curveFiberSize u = 4 then f 4 else 0) +
      (if curveFiberSize u = 19 then f 19 else 0) := by
    rcases curve_fiber_values u with h | h | h | h <;> simp [h]
  simp_rw [he]
  simp only [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul, h1, h2, h4, h19, Nat.cast_ofNat, Nat.cast_one, one_mul]

theorem decode_encodeCurveX (u : CurveCoordinate) :
    decodeCurveX (encodeCurveX u) = u := by
  funext i
  simp only [decodeCurveX, encodeCurveX, CW75LabelHierarchy.bPositionsX,
    CW75LabelHierarchy.bChoicesX]
  have hd : ∀ v : Fin 3,
      (if decide (v = 1) then (1 : Fin 3) else if decide (v ≠ 0) then 2 else 0) = v := by
    decide
  exact hd (u i)

theorem encodeCurveX_injective : Function.Injective encodeCurveX :=
  Function.LeftInverse.injective decode_encodeCurveX

theorem curve_incidentPrefix (s : CurveLeaf) :
    labelRecordOf curveLabels 3 s = encodeCurveX (CW75LabelHierarchy.x s) := rfl

theorem curve_incidentPrefix_entropy (p : FiniteLaw CurveLeaf) :
    finiteEntropy (p.map (labelRecordOf curveLabels 3)).mass =
      finiteEntropy (p.map CW75LabelHierarchy.x).mass := by
  classical
  have hmass : (p.map (labelRecordOf curveLabels 3)).mass =
      ((p.map CW75LabelHierarchy.x).map encodeCurveX).mass := by
    funext r
    by_cases hr : ∃ u, encodeCurveX u = r
    · obtain ⟨u, rfl⟩ := hr
      rw [FiniteLaw.map_mass_apply _ _ encodeCurveX_injective]
      simp only [FiniteLaw.map_mass, curve_incidentPrefix, encodeCurveX_injective.eq_iff]
    · have hn (u : CurveCoordinate) : encodeCurveX u ≠ r := fun h => hr ⟨u, h⟩
      simp [FiniteLaw.map_mass, curve_incidentPrefix, hn]
  rw [hmass]
  exact FiniteLaw.map_entropy_of_injective _ _ encodeCurveX_injective

theorem curveReaderPair_incident_prefix (n : Fin 5) :
    (curveReaderPair n = .xy ∨ curveReaderPair n = .xz) ↔ n.val < 3 := by
  fin_cases n <;> decide

theorem curveIncidentRate_eq_entropy_X (p : FiniteLaw CurveLeaf) :
    ConditionalLabels.lawPairingRate p curveLabels 5 curveReaderPair .xy +
      ConditionalLabels.lawPairingRate p curveLabels 5 curveReaderPair .xz =
        finiteEntropy (p.map CW75LabelHierarchy.x).mass := by
  rw [ConditionalLabels.incident_rate_eq_prefix_entropy p curveLabels 5 3
    (by decide) curveReaderPair curveReaderPair_incident_prefix]
  exact curve_incidentPrefix_entropy p

theorem curveHiddenRate_eq_entropy_sub_X (p : FiniteLaw CurveLeaf) :
    ConditionalLabels.lawPairingRate p curveLabels 5 curveReaderPair .yz =
      finiteEntropy p.mass - finiteEntropy (p.map CW75LabelHierarchy.x).mass := by
  rw [ConditionalLabels.remaining_rate_eq_entropy_sub_prefix p curveLabels 5 3
    (by decide) curveReaderPair curveReaderPair_incident_prefix curve_completeRecord_injective,
    curve_incidentPrefix_entropy]

end MatrixMultiplication.ComplexWitness

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_ComplexBounds_CW75ReorderedExecution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit complex square and rectangular matrix multiplication bounds. -/

noncomputable section

namespace MatrixMultiplication.CW75ReorderedExecution

open MatrixMultiplication.Foundation
open CW75LabelHierarchy CW75ReorderedWords ConditionalPrefixWords ComplexWitness
open PolynomialKernelExecution ExecutionPairingBudget StageHierarchyResources
open scoped BigOperators Classical

attribute [local irreducible] CW75LabelHierarchy.retainedWords

theorem realize_dimensions (counts : Scalar → ℕ) (t : ℕ) :
    (realize counts t).shape.rows =
        ConditionalLabels.stagePairingSize counts curveLabels 5 curveReaderPair .xz t ∧
    (realize counts t).shape.inner =
        ConditionalLabels.stagePairingSize counts curveLabels 5 curveReaderPair .xy t ∧
    (realize counts t).shape.columns =
        ConditionalLabels.stagePairingSize counts curveLabels 5 curveReaderPair .yz t := by
  have h (pair : ReaderPair) : pairingProduct counts t pair 5 =
      ConditionalLabels.stagePairingSize counts curveLabels 5 curveReaderPair pair t := by
    change (∏ i ∈ Finset.range 5,
      if readerPair i = pair then stageRefinementCount counts curveLabels i t else 1) =
      ∏ i : Fin 5,
        if readerPair i.val = pair then stageRefinementCount counts curveLabels i.val t else 1
    exact (Fin.prod_univ_eq_prod_range
      (fun i => if readerPair i = pair then
        stageRefinementCount counts curveLabels i t else 1) 5).symm
  exact ⟨(realize counts t).rows_exact.trans (h .xz),
    (realize counts t).inner_exact.trans (h .xy),
    (realize counts t).columns_exact.trans (h .yz)⟩

end MatrixMultiplication.CW75ReorderedExecution

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_ComplexBounds_CW75ReorderedFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit complex square and rectangular matrix multiplication bounds. -/

noncomputable section

namespace MatrixMultiplication.CW75ReorderedFinite

open MatrixMultiplication.Foundation CW75LabelHierarchy StageHierarchyResources
open ExecutionPairingBudget CW75ReorderedWords CW75ReorderedExecution ComplexWitness
open scoped BigOperators Classical

attribute [local irreducible] CW75LabelHierarchy.retainedWords

theorem dimensions_eq_pairingSize (counts : Scalar → ℕ) (t : ℕ) :
    rows counts t =
        ConditionalLabels.stagePairingSize counts curveLabels 5 curveReaderPair .xz t ∧
    inner counts t =
        ConditionalLabels.stagePairingSize counts curveLabels 5 curveReaderPair .xy t ∧
    columns counts t =
        ConditionalLabels.stagePairingSize counts curveLabels 5 curveReaderPair .yz t :=
  realize_dimensions counts t

end MatrixMultiplication.CW75ReorderedFinite

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_ComplexBounds_CW75ReorderedFiniteRates
attribute [-simp] _root_.OAI.MatrixMultiplication.CW75ReorderedBalanced.witness_inner _root_.OAI.MatrixMultiplication.CW75ReorderedBalanced.witness_multiplicity _root_.OAI.MatrixMultiplication.CW75ReorderedBalanced.witness_outer _root_.OAI.MatrixMultiplication.CW75ReorderedBalanced.witness_rank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit complex square and rectangular matrix multiplication bounds. -/

noncomputable section

namespace MatrixMultiplication.CW75ReorderedFiniteRates

open MatrixMultiplication.Foundation CW75LabelHierarchy StageHierarchyResources
open CW75ReorderedFinite ComplexWitness Filter
open scoped BigOperators Topology Classical

theorem tendsto_log_copies (counts : Scalar → ℕ) (hD : 0 < ∑ a, counts a)
    (p : FiniteLaw Scalar)
    (mass : ∀ a, p.mass a = (counts a : ℝ) / (∑ b, counts b : ℕ)) :
    Tendsto (fun t : ℕ => Real.log (copies counts t : ℝ) /
      ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (finiteEntropy p.mass)) := by
  have hmass : (fun a => (counts a : ℝ) / (∑ b, counts b : ℕ)) = p.mass :=
    (funext mass).symm
  simpa only [copies, hmass] using tendsto_log_exactWords_card_mul counts hD

theorem tendsto_log_auxiliaryBudget (counts : Scalar → ℕ) (hD : 0 < ∑ a, counts a)
    (p : FiniteLaw Scalar)
    (mass : ∀ a, p.mass a = (counts a : ℝ) / (∑ b, counts b : ℕ)) :
    Tendsto (fun t : ℕ => Real.log (stageAuxiliaryBudget counts curveLabels 5 t : ℝ) /
      ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (finiteEntropy p.mass)) := by
  have hmass : (fun a => (counts a : ℝ) / (∑ b, counts b : ℕ)) = p.mass :=
    (funext mass).symm
  simpa only [hmass] using tendsto_log_stageAuxiliaryBudget counts hD curveLabels 5
    curve_completeRecord_injective

theorem tendsto_log_sourceRank (counts : Scalar → ℕ) (hD : 0 < ∑ a, counts a) :
    Tendsto (fun t : ℕ => Real.log ((27 ^ blocks counts t : ℕ) : ℝ) /
      ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (3 * Real.log 3)) := by
  have hlog27 : Real.log (27 : ℝ) = 3 * Real.log 3 := by
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have hD' : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with t ht
  have htD : (t : ℝ) * (∑ a, counts a : ℕ) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr ht) hD'
  rw [Nat.cast_pow, Real.log_pow, blocks, Nat.cast_mul]
  change 3 * Real.log 3 =
    ((t : ℝ) * (∑ a, counts a : ℕ)) * Real.log 27 /
      ((t : ℝ) * (∑ a, counts a : ℕ))
  rw [mul_div_cancel_left₀ _ htD, hlog27]

theorem tendsto_log_rankBudget (counts : Scalar → ℕ) (hD : 0 < ∑ a, counts a)
    (p : FiniteLaw Scalar)
    (mass : ∀ a, p.mass a = (counts a : ℝ) / (∑ b, counts b : ℕ)) :
    Tendsto (fun t : ℕ => Real.log (rankBudget counts t : ℝ) /
      ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (3 * Real.log 3 + finiteEntropy p.mass)) := by
  apply ((tendsto_log_sourceRank counts hD).add
    (tendsto_log_auxiliaryBudget counts hD p mass)).congr
  intro t
  have hsource : ((27 ^ blocks counts t : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pow_ne_zero _ (by decide))
  have hauxiliary : (stageAuxiliaryBudget counts curveLabels 5 t : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr
      (Nat.ne_of_gt (stageAuxiliaryBudget_pos counts curveLabels 5 t))
  rw [rankBudget, Nat.cast_mul, Real.log_mul hsource hauxiliary, add_div]

end MatrixMultiplication.CW75ReorderedFiniteRates

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Numerical_ComplexLogThreeCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact rational intervals, logarithm bounds and arithmetic circuit soundness. -/

namespace MatrixMultiplication.Foundation

theorem log_three_upper : Real.log 3 < (1098612289 : ℝ) / 10 ^ 9 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 3)).2
  refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 16)
  norm_num [Finset.sum_range_succ, Nat.factorial]

end MatrixMultiplication.Foundation

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

theorem log_three_upper : Real.log 3 < (10987 : ℝ) / 10000 := by
  have h := MatrixMultiplication.Foundation.log_three_upper
  norm_num at h ⊢
  linarith

theorem log_nineteen_bounds :
    (7361 : ℝ) / 2500 < Real.log 19 ∧ Real.log 19 < (5889 : ℝ) / 2000 := by
  have h := log_bounds_of_reduction reduceNineteen (7361 / 2500) (5889 / 2000)
    (by decide +kernel) (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem log_curve_lower :
    (77953 : ℝ) / 20000 < Real.log ((246439 : ℝ) / 5000) := by
  have h := log_bounds_of_reduction reduceCurveLo (77953 / 20000) (97443 / 25000)
    (by decide +kernel) (by decide +kernel)
  norm_num at h ⊢
  exact h.1

theorem log_curve_upper :
    Real.log ((49289 : ℝ) / 1000) < (97443 : ℝ) / 25000 := by
  have h := log_bounds_of_reduction reduceCurveHi (77953 / 20000) (97443 / 25000)
    (by decide +kernel) (by decide +kernel)
  norm_num at h ⊢
  exact h.2

end MatrixMultiplication.ComplexCertificates

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Numerical_ComplexCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact rational intervals, logarithm bounds and arithmetic circuit soundness. -/

noncomputable section

namespace MatrixMultiplication.ComplexCertificates

theorem curveU_cube : curveU ^ 3 = 4 := by
  rw [curveU, ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem curveV_cube : curveV ^ 3 = 361 := by
  rw [curveV, ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 19)]
  norm_num

theorem curveU_bounds :
    (158739 : ℝ) / 100000 < curveU ∧ curveU < (79371 : ℝ) / 50000 := by
  have h0 : 0 ≤ curveU := Real.rpow_nonneg (by norm_num) _
  constructor
  · apply (pow_lt_pow_iff_left₀ (by norm_num) h0 (by norm_num : (3 : ℕ) ≠ 0)).1
    rw [curveU_cube]
    norm_num
  · apply (pow_lt_pow_iff_left₀ h0 (by norm_num) (by norm_num : (3 : ℕ) ≠ 0)).1
    rw [curveU_cube]
    norm_num

theorem curveV_bounds :
    (71203 : ℝ) / 10000 < curveV ∧ curveV < (14241 : ℝ) / 2000 := by
  have h0 : 0 ≤ curveV := Real.rpow_nonneg (by norm_num) _
  constructor
  · apply (pow_lt_pow_iff_left₀ (by norm_num) h0 (by norm_num : (3 : ℕ) ≠ 0)).1
    rw [curveV_cube]
    norm_num
  · apply (pow_lt_pow_iff_left₀ h0 (by norm_num) (by norm_num : (3 : ℕ) ≠ 0)).1
    rw [curveV_cube]
    norm_num

theorem curveZ_bounds :
    (246439 : ℝ) / 5000 < curveZ ∧ curveZ < (49289 : ℝ) / 1000 := by
  obtain ⟨hu, hu'⟩ := curveU_bounds
  obtain ⟨hv, hv'⟩ := curveV_bounds
  have hu0 : 0 ≤ curveU := by linarith
  constructor
  · have h : 8 + 12 * ((158739 : ℝ) / 100000) +
        6 * ((158739 : ℝ) / 100000) ^ 2 + (71203 : ℝ) / 10000 ≤ curveZ := by
      dsimp [curveZ]
      gcongr
    norm_num at h ⊢
    linarith
  · have h : curveZ ≤ 8 + 12 * ((79371 : ℝ) / 50000) +
        6 * ((79371 : ℝ) / 50000) ^ 2 + (14241 : ℝ) / 2000 := by
      dsimp [curveZ]
      gcongr
    norm_num at h ⊢
    linarith

theorem curveG_bounds :
    (27961 : ℝ) / 25000 < curveG ∧ curveG < (6991 : ℝ) / 6250 := by
  obtain ⟨hu, hu'⟩ := curveU_bounds
  obtain ⟨hv, hv'⟩ := curveV_bounds
  obtain ⟨hz, hz'⟩ := curveZ_bounds
  obtain ⟨hl2, hh2⟩ := log_two_bounds
  obtain ⟨hl19, hh19⟩ := log_nineteen_bounds
  have hu0 : 0 ≤ curveU := by linarith
  have hv0 : 0 ≤ curveV := by linarith
  have hz0 : 0 < curveZ := by linarith
  have hl20 : 0 ≤ Real.log 2 := by linarith
  have hl190 : 0 ≤ Real.log 19 := by linarith
  have hnlo :
      12 * ((158739 : ℝ) / 100000) * (1 + (158739 : ℝ) / 100000) *
        ((34657 : ℝ) / 50000) + ((71203 : ℝ) / 10000) * ((7361 : ℝ) / 2500) ≤
      12 * curveU * (1 + curveU) * Real.log 2 + curveV * Real.log 19 := by
    gcongr
  have hnhi :
      12 * curveU * (1 + curveU) * Real.log 2 + curveV * Real.log 19 ≤
      12 * ((79371 : ℝ) / 50000) * (1 + (79371 : ℝ) / 50000) *
        ((17329 : ℝ) / 25000) + ((14241 : ℝ) / 2000) * ((5889 : ℝ) / 2000) := by
    gcongr
  constructor
  · apply (lt_div_iff₀ hz0).2
    norm_num at hnlo
    nlinarith
  · apply (div_lt_iff₀ hz0).2
    norm_num at hnhi
    nlinarith

theorem curveH_bounds :
    (31519 : ℝ) / 10000 < curveH ∧ curveH < (15761 : ℝ) / 5000 := by
  obtain ⟨hg, hg'⟩ := curveG_bounds
  obtain ⟨hz, hz'⟩ := curveZ_bounds
  have hz0 : 0 < curveZ := by linarith
  have hlo : (77953 : ℝ) / 20000 < Real.log curveZ :=
    log_curve_lower.trans (Real.log_lt_log (by norm_num) hz)
  have hhi : Real.log curveZ < (97443 : ℝ) / 25000 :=
    (Real.log_lt_log hz0 hz').trans log_curve_upper
  dsimp [curveH]
  constructor <;> linarith

end MatrixMultiplication.ComplexCertificates

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Rectangular_Growth
attribute [-simp] _root_.OAI.MatrixMultiplication.Arithmetic.RecursiveBlock.Family.cost_ofMatrix
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
attribute [-simp] _root_.OAI.MatrixMultiplication.Foundation.ExecutionPairingBudget.MatrixCoordinates.standard_tensor
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
-- module Solutions.Q235_MM.MatrixMultiplication_Rectangular_Witness
attribute [-simp] _root_.OAI.MatrixMultiplication.CW75ReorderedBalanced.witness_inner _root_.OAI.MatrixMultiplication.CW75ReorderedBalanced.witness_multiplicity _root_.OAI.MatrixMultiplication.CW75ReorderedBalanced.witness_outer _root_.OAI.MatrixMultiplication.CW75ReorderedBalanced.witness_rank _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_inner _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_multiplicity _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_outer _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_rank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rectangular matrix multiplication algorithms and their asymptotic exponents. -/

namespace MatrixMultiplication.RectangularWitness

open Filter
open scoped Topology

theorem aspect_lower {g h : ℝ}
    (hg : (27961 : ℝ) / 25000 < g)
    (hh₀ : 0 < h) (hh : h < (15761 : ℝ) / 5000) :
    (55922 : ℝ) / 78805 < 2 * g / h := by
  apply (lt_div_iff₀ hh₀).2
  nlinarith

theorem target_aspect_lt {g h : ℝ}
    (hg : (27961 : ℝ) / 25000 < g)
    (hh₀ : 0 < h) (hh : h < (15761 : ℝ) / 5000) :
    (709 : ℝ) / 1000 < 2 * g / h := by
  exact (by norm_num : (709 : ℝ) / 1000 < 55922 / 78805).trans
    (aspect_lower hg hh₀ hh)

theorem exponent_upper {c h : ℝ}
    (hc : c < (10987 : ℝ) / 10000)
    (hh : (31519 : ℝ) / 10000 < h) :
    6 * c / h < (65922 : ℝ) / 31519 := by
  have hh₀ : 0 < h := by linarith
  apply (div_lt_iff₀ hh₀).2
  nlinarith

theorem exponent_lt_target {c h : ℝ}
    (hc : c < (10987 : ℝ) / 10000)
    (hh : (31519 : ℝ) / 10000 < h) :
    6 * c / h < (523 : ℝ) / 250 := by
  exact (exponent_upper hc hh).trans
    (by norm_num : (65922 : ℝ) / 31519 < 523 / 250)

theorem omega_lt_of_balanced_family
    (W : ℕ → ComplexWitness.FiniteRectangularWitness)
    (scale : ℕ → ℝ) (k target g h H : ℝ)
    (k_nonneg : 0 ≤ k) (h_positive : 0 < h)
    (aspect_gap : k * h < 2 * g) (cost_gap : 6 * Real.log 3 < target * h)
    (scale_positive : ∀ᶠ n in atTop, 0 < scale n)
    (outer_rate : Tendsto
      (fun n => Real.log ((W n).outer : ℝ) / scale n) atTop (𝓝 h))
    (inner_rate : Tendsto
      (fun n => Real.log ((W n).inner : ℝ) / scale n) atTop (𝓝 (2 * g)))
    (multiplicity_rate : Tendsto
      (fun n => Real.log ((W n).multiplicity : ℝ) / scale n) atTop (𝓝 (2 * H)))
    (rank_rate : Tendsto
      (fun n => Real.log ((W n).rank : ℝ) / scale n) atTop
      (𝓝 (6 * Real.log 3 + 2 * H))) :
    Arithmetic.rectangularOmega ℂ k < target := by
  have hbound := RectangularRateLimit.exponent_le_of_finite_asi
    (fun n => (W n).outer_pos) (fun n => (W n).inner_pos)
    scale_positive outer_rate inner_rate multiplicity_rate rank_rate h_positive aspect_gap
    (fun n ha hab => Arithmetic.equalRectangular_log_inequality_of_polynomialApproximation
      ha (W n).multiplicity_pos k_nonneg hab (W n).approximation)
  have hcancel : (6 * Real.log 3 + 2 * H - 2 * H) / h = 6 * Real.log 3 / h := by ring
  rw [hcancel] at hbound
  exact hbound.trans_lt ((div_lt_iff₀ h_positive).2 cost_gap)

theorem omega_lt_target_of_nearby_balanced_family
    (W : ℕ → ComplexWitness.FiniteRectangularWitness)
    (scale : ℕ → ℝ) (g h H : ℝ)
    (g_lower : (27961 : ℝ) / 25000 < g)
    (h_lower : (31519 : ℝ) / 10000 < h)
    (h_upper : h < (15761 : ℝ) / 5000)
    (scale_positive : ∀ᶠ n in atTop, 0 < scale n)
    (outer_rate : Tendsto
      (fun n => Real.log ((W n).outer : ℝ) / scale n) atTop
      (𝓝 h))
    (inner_rate : Tendsto
      (fun n => Real.log ((W n).inner : ℝ) / scale n) atTop
      (𝓝 (2 * g)))
    (multiplicity_rate : Tendsto
      (fun n => Real.log ((W n).multiplicity : ℝ) / scale n) atTop (𝓝 (2 * H)))
    (rank_rate : Tendsto
      (fun n => Real.log ((W n).rank : ℝ) / scale n) atTop
      (𝓝 (6 * Real.log 3 + 2 * H))) :
    Arithmetic.rectangularOmega ℂ ((709 : ℝ) / 1000) < (523 : ℝ) / 250 := by
  have hh₀ : 0 < h := by linarith
  have hgap : (709 : ℝ) / 1000 * h < 2 * g :=
    (lt_div_iff₀ hh₀).1 (target_aspect_lt g_lower hh₀ h_upper)
  apply omega_lt_of_balanced_family W scale (709 / 1000) (523 / 250) g h H
    (by norm_num) hh₀ hgap _ scale_positive outer_rate inner_rate multiplicity_rate rank_rate
  exact (div_lt_iff₀ hh₀).1
    (exponent_lt_target ComplexCertificates.log_three_upper h_lower)

end MatrixMultiplication.RectangularWitness

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_ComplexBounds_CW75ReorderedBalancedRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit complex square and rectangular matrix multiplication bounds. -/

noncomputable section

namespace MatrixMultiplication.CW75ReorderedBalancedRates

open MatrixMultiplication.Foundation Filter CW75LabelHierarchy
open ConditionalLabels ComplexWitness CW75ReorderedBalanced
open scoped BigOperators Topology Classical

variable (counts : Scalar → ℕ) (hD : 0 < ∑ a, counts a)
  (p : FiniteLaw Scalar)
  (mass : ∀ a, p.mass a = (counts a : ℝ) / (∑ b, counts b : ℕ))

include hD mass

theorem tendsto_log_rows :
    Tendsto (fun t => Real.log (CW75ReorderedFinite.rows counts t : ℝ) /
      ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (lawPairingRate p curveLabels 5 curveReaderPair .xz)) := by
  have h := tendsto_log_stagePairingSize_law counts hD p mass
    curveLabels 5 curveReaderPair .xz
  apply h.congr
  intro t
  rw [(CW75ReorderedFinite.dimensions_eq_pairingSize counts t).1]

theorem tendsto_log_inner :
    Tendsto (fun t => Real.log (CW75ReorderedFinite.inner counts t : ℝ) /
      ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (lawPairingRate p curveLabels 5 curveReaderPair .xy)) := by
  have h := tendsto_log_stagePairingSize_law counts hD p mass
    curveLabels 5 curveReaderPair .xy
  apply h.congr
  intro t
  rw [(CW75ReorderedFinite.dimensions_eq_pairingSize counts t).2.1]

theorem tendsto_log_columns :
    Tendsto (fun t => Real.log (CW75ReorderedFinite.columns counts t : ℝ) /
      ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (lawPairingRate p curveLabels 5 curveReaderPair .yz)) := by
  have h := tendsto_log_stagePairingSize_law counts hD p mass
    curveLabels 5 curveReaderPair .yz
  apply h.congr
  intro t
  rw [(CW75ReorderedFinite.dimensions_eq_pairingSize counts t).2.2]

theorem tendsto_log_witness_outer :
    Tendsto (fun t => Real.log ((witness counts t).outer : ℝ) /
      ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (lawPairingRate p curveLabels 5 curveReaderPair .xy +
        lawPairingRate p curveLabels 5 curveReaderPair .xz)) := by
  have h := (tendsto_log_rows counts hD p mass).add
    (tendsto_log_inner counts hD p mass)
  rw [add_comm (lawPairingRate p curveLabels 5 curveReaderPair .xz)] at h
  apply h.congr
  intro t
  rw [witness_outer, Nat.cast_mul, Real.log_mul
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (CW75ReorderedFinite.rows_pos counts t)))
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (CW75ReorderedFinite.inner_pos counts t))), add_div]

theorem tendsto_log_witness_inner :
    Tendsto (fun t => Real.log ((witness counts t).inner : ℝ) /
      ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (2 * lawPairingRate p curveLabels 5 curveReaderPair .yz)) := by
  simpa only [witness_inner, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat,
    mul_div_assoc] using (tendsto_log_columns counts hD p mass).const_mul 2

theorem tendsto_log_witness_multiplicity :
    Tendsto (fun t => Real.log ((witness counts t).multiplicity : ℝ) /
      ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (2 * finiteEntropy p.mass)) := by
  simpa only [witness_multiplicity, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat,
    mul_div_assoc] using
      (CW75ReorderedFiniteRates.tendsto_log_copies counts hD p mass).const_mul 2

theorem tendsto_log_witness_rank :
    Tendsto (fun t => Real.log ((witness counts t).rank : ℝ) /
      ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (6 * Real.log 3 + 2 * finiteEntropy p.mass)) := by
  have h := (CW75ReorderedFiniteRates.tendsto_log_rankBudget counts hD p mass).const_mul 2
  have hcost : 2 * (3 * Real.log 3 + finiteEntropy p.mass) =
      6 * Real.log 3 + 2 * finiteEntropy p.mass := by ring
  simpa only [witness_rank, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat,
    mul_div_assoc, hcost] using h

omit mass

theorem scale_eventually_pos :
    ∀ᶠ t : ℕ in atTop, 0 < (t : ℝ) * (∑ a, counts a : ℕ) := by
  filter_upwards [eventually_ge_atTop 1] with t ht
  exact mul_pos (Nat.cast_pos.mpr (by omega)) (Nat.cast_pos.mpr hD)

end MatrixMultiplication.CW75ReorderedBalancedRates

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

end MatrixMultiplication.ConditionalLabels

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Entropy_CurveLaws
attribute [-simp] _root_.OAI.MatrixMultiplication.CompletionProductLaws.independentProduct_mass _root_.OAI.MatrixMultiplication.CompletionProductLaws.sigmaJoint_mass _root_.OAI.MatrixMultiplication.ConditionalLabels.normalizedCountLaw_mass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.CurveLaws

open MatrixMultiplication.Foundation ComplexWitness

theorem uniformLift_marginal (p : FiniteLaw CurveCoordinate) (u : CurveCoordinate) :
    ((uniformLift p).map CW75LabelHierarchy.x).mass u = p.mass u := by
  classical
  rw [FiniteLaw.map_mass]
  change (∑ s : CurveLeaf,
    if CW75LabelHierarchy.x s = u then
      p.mass (CW75LabelHierarchy.x s) / curveFiberSize (CW75LabelHierarchy.x s)
    else 0) = p.mass u
  rw [sum_curveLeaves_by_X
    (fun v => if v = u then p.mass v / (curveFiberSize v : ℝ) else 0)]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  exact mul_div_cancel₀ (p.mass u) (fiberSize_real_pos u).ne'

theorem entropyTerm_div_fiber (p : ℝ) {d : ℝ} (hd : 0 < d) :
    d * entropyTerm (p / d) = entropyTerm p + p * Real.log d := by
  by_cases hp : p = 0
  · simp [hp]
  · rw [entropyTerm, Real.log_div hp hd.ne', entropyTerm]
    field_simp [hd.ne']
    ring

theorem uniformLift_entropy (p : FiniteLaw CurveCoordinate) :
    finiteEntropy (uniformLift p).mass = finiteEntropy p.mass +
      ∑ u : CurveCoordinate, p.mass u * Real.log (curveFiberSize u) := by
  change (∑ s : CurveLeaf,
    entropyTerm (p.mass (CW75LabelHierarchy.x s) /
      curveFiberSize (CW75LabelHierarchy.x s))) = _
  rw [sum_curveLeaves_by_X
    (fun u => entropyTerm (p.mass u / (curveFiberSize u : ℝ)))]
  simp_rw [entropyTerm_div_fiber _ (fiberSize_real_pos _)]
  simp only [finiteEntropy, Finset.sum_add_distrib]

theorem partition_closed (t : ℝ) :
    partition t = 8 + 12 * (2 : ℝ) ^ t + 6 * (4 : ℝ) ^ t + (19 : ℝ) ^ t := by
  rw [partition, sum_curveFiberSizes (fun d => (d : ℝ) ^ t)]
  simp

theorem marginal_of_leafLaw (t : ℝ) :
    ((leafLaw t).map CW75LabelHierarchy.x).mass = (marginal t).mass := by
  funext u
  exact uniformLift_marginal (marginal t) u

theorem log_marginal (t : ℝ) (u : CurveCoordinate) :
    Real.log ((marginal t).mass u) =
      t * Real.log (curveFiberSize u) - Real.log (partition t) := by
  change Real.log ((curveFiberSize u : ℝ) ^ t / partition t) = _
  rw [Real.log_div (Real.rpow_pos_of_pos (fiberSize_real_pos u) t).ne'
    (partition_pos t).ne', Real.log_rpow (fiberSize_real_pos u)]

theorem incident_entropy (t : ℝ) : finiteEntropy (marginal t).mass = incident t := by
  unfold finiteEntropy
  simp_rw [entropyTerm, log_marginal]
  calc
    (∑ u : CurveCoordinate,
      -(marginal t).mass u *
        (t * Real.log (curveFiberSize u) - Real.log (partition t))) =
      (∑ u : CurveCoordinate, (marginal t).mass u) * Real.log (partition t) -
        t * ∑ u : CurveCoordinate,
          (marginal t).mass u * Real.log (curveFiberSize u) := by
      simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ = incident t := by rw [(marginal t).total]; simp [incident, hidden]

theorem leaf_entropy (t : ℝ) :
    finiteEntropy (leafLaw t).mass = incident t + hidden t := by
  rw [leafLaw, uniformLift_entropy, incident_entropy]
  rfl

theorem conditional_entropy (t : ℝ) :
    finiteEntropy (leafLaw t).mass -
      finiteEntropy ((leafLaw t).map CW75LabelHierarchy.x).mass = hidden t := by
  rw [marginal_of_leafLaw, leaf_entropy, incident_entropy]
  ring

theorem hidden_closed (t : ℝ) :
    hidden t =
      (12 * (2 : ℝ) ^ t * Real.log 2 + 6 * (4 : ℝ) ^ t * Real.log 4 +
        (19 : ℝ) ^ t * Real.log 19) / partition t := by
  unfold hidden
  change (∑ u : CurveCoordinate,
    ((curveFiberSize u : ℝ) ^ t / partition t) * Real.log (curveFiberSize u)) = _
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, sum_curveFiberSizes (fun d => (d : ℝ) ^ t * Real.log d)]
  simp
  ring

theorem incident_rate (t : ℝ) :
    ConditionalLabels.lawPairingRate (leafLaw t) curveLabels 5 curveReaderPair .xy +
      ConditionalLabels.lawPairingRate (leafLaw t) curveLabels 5 curveReaderPair .xz =
        incident t := by
  rw [curveIncidentRate_eq_entropy_X, marginal_of_leafLaw, incident_entropy]

theorem hidden_rate (t : ℝ) :
    ConditionalLabels.lawPairingRate (leafLaw t) curveLabels 5 curveReaderPair .yz =
      hidden t := by
  rw [curveHiddenRate_eq_entropy_sub_X]
  exact conditional_entropy t

end MatrixMultiplication.CurveLaws

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Numerical_CurveLawsCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact rational intervals, logarithm bounds and arithmetic circuit soundness. -/

noncomputable section

namespace MatrixMultiplication.CurveLaws

open ComplexWitness

theorem rpow_four (t : ℝ) : (4 : ℝ) ^ t = ((2 : ℝ) ^ t) ^ 2 := by
  rw [show (4 : ℝ) = 2 * 2 by norm_num,
    Real.mul_rpow (by norm_num) (by norm_num), pow_two]

theorem log_four : Real.log (4 : ℝ) = 2 * Real.log 2 := by
  calc
    Real.log (4 : ℝ) = Real.log ((2 : ℝ) * 2) := by norm_num
    _ = Real.log 2 + Real.log 2 := Real.log_mul (by norm_num) (by norm_num)
    _ = 2 * Real.log 2 := by ring

theorem partition_two_thirds : partition (2 / 3 : ℝ) = ComplexCertificates.curveZ := by
  rw [partition_closed, rpow_four]
  rfl

theorem hidden_two_thirds : hidden (2 / 3 : ℝ) = ComplexCertificates.curveG := by
  rw [hidden_closed, partition_two_thirds, rpow_four, log_four]
  unfold ComplexCertificates.curveG ComplexCertificates.curveU ComplexCertificates.curveV
  ring

theorem incident_two_thirds : incident (2 / 3 : ℝ) = ComplexCertificates.curveH := by
  rw [incident, partition_two_thirds, hidden_two_thirds]
  rfl

theorem incident_rate_two_thirds :
    ConditionalLabels.lawPairingRate (leafLaw (2 / 3 : ℝ))
        curveLabels 5 curveReaderPair .xy +
      ConditionalLabels.lawPairingRate (leafLaw (2 / 3 : ℝ))
        curveLabels 5 curveReaderPair .xz = ComplexCertificates.curveH := by
  rw [incident_rate, incident_two_thirds]

theorem hidden_rate_two_thirds :
    ConditionalLabels.lawPairingRate (leafLaw (2 / 3 : ℝ))
      curveLabels 5 curveReaderPair .yz = ComplexCertificates.curveG := by
  rw [hidden_rate, hidden_two_thirds]

end MatrixMultiplication.CurveLaws

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Entropy_CurveRationalLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

namespace MatrixMultiplication.CurveLaws

open MatrixMultiplication.Foundation ComplexWitness ConditionalLabels Filter
open scoped BigOperators Topology

theorem exists_rational_rate_bounds :
    ∃ q : RationalLaw CurveLeaf,
      (31519 : ℝ) / 10000 <
        lawPairingRate q.toFiniteLaw curveLabels 5 curveReaderPair .xy +
          lawPairingRate q.toFiniteLaw curveLabels 5 curveReaderPair .xz ∧
      lawPairingRate q.toFiniteLaw curveLabels 5 curveReaderPair .xy +
          lawPairingRate q.toFiniteLaw curveLabels 5 curveReaderPair .xz <
        (15761 : ℝ) / 5000 ∧
      (27961 : ℝ) / 25000 <
        lawPairingRate q.toFiniteLaw curveLabels 5 curveReaderPair .yz ∧
      lawPairingRate q.toFiniteLaw curveLabels 5 curveReaderPair .yz <
        (6991 : ℝ) / 6250 := by
  obtain ⟨q, hq⟩ := exists_rational_law_sequence (leafLaw (2 / 3 : ℝ))
  have hi := (tendsto_lawPairingRate hq curveLabels 5 curveReaderPair .xy).add
    (tendsto_lawPairingRate hq curveLabels 5 curveReaderPair .xz)
  have hh := tendsto_lawPairingRate hq curveLabels 5 curveReaderPair .yz
  rw [incident_rate_two_thirds] at hi
  rw [hidden_rate_two_thirds] at hh
  have hilo := hi.eventually_const_lt ComplexCertificates.curveH_bounds.1
  have hihi := hi.eventually_lt_const ComplexCertificates.curveH_bounds.2
  have hhlo := hh.eventually_const_lt ComplexCertificates.curveG_bounds.1
  have hhhi := hh.eventually_lt_const ComplexCertificates.curveG_bounds.2
  obtain ⟨n, hn⟩ := (hilo.and (hihi.and (hhlo.and hhhi))).exists
  exact ⟨q n, hn⟩

theorem exists_count_rate_bounds :
    ∃ counts : CurveLeaf → ℕ, ∃ hD : 0 < ∑ a, counts a,
      (31519 : ℝ) / 10000 <
        lawPairingRate (normalizedCountLaw counts hD) curveLabels 5 curveReaderPair .xy +
          lawPairingRate (normalizedCountLaw counts hD) curveLabels 5 curveReaderPair .xz ∧
      lawPairingRate (normalizedCountLaw counts hD) curveLabels 5 curveReaderPair .xy +
          lawPairingRate (normalizedCountLaw counts hD) curveLabels 5 curveReaderPair .xz <
        (15761 : ℝ) / 5000 ∧
      (27961 : ℝ) / 25000 <
        lawPairingRate (normalizedCountLaw counts hD) curveLabels 5 curveReaderPair .yz ∧
      lawPairingRate (normalizedCountLaw counts hD) curveLabels 5 curveReaderPair .yz <
        (6991 : ℝ) / 6250 := by
  obtain ⟨q, hq⟩ := exists_rational_rate_bounds
  obtain ⟨counts, hD, hmass⟩ := q.exists_type_representation
  have law_eq (p r : FiniteLaw CurveLeaf) (h : p.mass = r.mass) : p = r := by
    cases p
    cases r
    cases h
    rfl
  have heq : normalizedCountLaw counts hD = q.toFiniteLaw :=
    law_eq _ _ (funext hmass)
  refine ⟨counts, hD, ?_⟩
  simpa only [heq] using hq

end MatrixMultiplication.CurveLaws

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_ComplexBounds_CW75ReorderedRectangular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit complex square and rectangular matrix multiplication bounds. -/

namespace MatrixMultiplication.CW75ReorderedRectangular

open MatrixMultiplication.Foundation ConditionalLabels ComplexWitness
open CW75ReorderedBalanced CW75ReorderedBalancedRates
open scoped BigOperators

theorem rectangularOmega_lt_target :
    Arithmetic.rectangularOmega ℂ ((709 : ℝ) / 1000) < (523 : ℝ) / 250 := by
  obtain ⟨counts, hD, h_lower, h_upper, g_lower, _g_upper⟩ :=
    CurveLaws.exists_count_rate_bounds
  let p := normalizedCountLaw counts hD
  have mass : ∀ a, p.mass a = (counts a : ℝ) / (∑ b, counts b : ℕ) := fun _ => rfl
  exact RectangularWitness.omega_lt_target_of_nearby_balanced_family
    (witness counts) (fun t => (t : ℝ) * (∑ a, counts a : ℕ))
    (lawPairingRate p curveLabels 5 curveReaderPair .yz)
    (lawPairingRate p curveLabels 5 curveReaderPair .xy +
      lawPairingRate p curveLabels 5 curveReaderPair .xz)
    (finiteEntropy p.mass) g_lower h_lower h_upper
    (scale_eventually_pos counts hD)
    (tendsto_log_witness_outer counts hD p mass)
    (tendsto_log_witness_inner counts hD p mass)
    (tendsto_log_witness_multiplicity counts hD p mass)
    (tendsto_log_witness_rank counts hD p mass)

end MatrixMultiplication.CW75ReorderedRectangular

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_HiddenInstances
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype
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

end MatrixMultiplication.DualHiddenRates

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

/-- Multiplication of `n × n^0.709` by `n^0.709 × n` complex matrices has
arithmetic exponent less than `2.092`. -/
theorem complex_rectangular_omega_lt_523_div_250_oai :
    Arithmetic.rectangularOmega ℂ ((709 : ℝ) / 1000) < (523 : ℝ) / 250 :=
  CW75ReorderedRectangular.rectangularOmega_lt_target

end MatrixMultiplication

end OAI
end

theorem solution : type_of% @OAI.MatrixMultiplication.complex_rectangular_omega_lt_523_div_250_oai := @OAI.MatrixMultiplication.complex_rectangular_omega_lt_523_div_250_oai
