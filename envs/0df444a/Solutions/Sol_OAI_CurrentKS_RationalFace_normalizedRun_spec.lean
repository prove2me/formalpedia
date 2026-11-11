-- Prove2me | solution 1 for OAI.CurrentKS.RationalFace.normalizedRun_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:52:06.385198+00:00
-- url     : https://prove2.me/submissions/563dbae9-6b10-4bfc-aec8-978b8497cc46

import Mathlib
import Definitions.Def_OAIQ241TT006
import Theorems.Thm_OAI_CurrentKS_RationalFace_transition_spec

section
-- module Solutions.OAIQ241_TT.Compat
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
/-- Mathlib d13f23b's `CStarAlgebra.norm_le_norm_of_le_of_nonneg hab ha`; ours is `norm_le_norm_of_nonneg_of_le ha hab`. -/
theorem _root_.CStarAlgebra.norm_le_norm_of_le_of_nonneg {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {a b : A} (hab : a ≤ b) (ha : 0 ≤ a) : ‖a‖ ≤ ‖b‖ :=
  CStarAlgebra.norm_le_norm_of_nonneg_of_le ha hab
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_Realification
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W08.realifyVector_complexify _root_.OAI.KS.W08.realifyVector_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W08

open Matrix
open scoped BigOperators

theorem realify_injective {m n : Type*} :
    Function.Injective (@realify m n) := by
  intro A B h
  apply Matrix.ext
  intro i j
  apply Complex.ext
  · exact congrFun (congrFun h (Sum.inl i)) (Sum.inl j)
  · exact congrFun (congrFun h (Sum.inr i)) (Sum.inl j)

theorem realify_mul {m n p : Type*} [Fintype n]
    (A : Matrix m n ℂ) (B : Matrix n p ℂ) :
    realify (A * B) = realify A * realify B := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [realify, Matrix.fromBlocks, Matrix.mul_apply, Fintype.sum_sum_type, Complex.mul_re,
      Complex.mul_im, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_neg_distrib] <;> ring

theorem realify_mulVec {m n : Type*} [Fintype n]
    (A : Matrix m n ℂ) (v : n → ℂ) :
    realifyVector (A *ᵥ v) = realify A *ᵥ realifyVector v := by
  funext i
  rcases i with i | i <;>
    simp [realifyVector, realify, Matrix.fromBlocks, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Complex.mul_re, Complex.mul_im, Finset.sum_add_distrib,
      Finset.sum_sub_distrib] <;> ring

end KS.W08

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RealifyAdd
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace KS.W08
open Matrix
open scoped BigOperators

variable {m n p : Type*}

lemma realify_add (A B : Matrix m n ℂ) : realify (A+B)=realify A+realify B := by
  ext i j
  cases i <;> cases j <;> simp [realify, Matrix.fromBlocks, neg_add_rev, add_comm]
lemma realify_zero : realify (0 : Matrix m n ℂ)=0 := by
  ext i j
  cases i <;> cases j <;> simp [realify, Matrix.fromBlocks]
lemma realify_smul (r : ℝ) (A : Matrix m n ℂ) : realify (r • A)=r • realify A := by
  ext i j
  cases i <;> cases j <;> simp [realify, Matrix.fromBlocks]
lemma realify_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix m n ℂ) :
    realify (∑ i ∈ s,A i)=∑ i ∈ s,realify (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [realify_zero]
  | @insert a s ha ih => simp only [Finset.sum_insert ha,realify_add,ih]
end KS.W08

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_ScalarPsi
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Scalar
noncomputable section
open scoped ContDiff

lemma base_pos {x : ℝ} (hx : |x| < 1) : 0 < 1-x^2 := by
  have h := (abs_lt.mp hx)
  nlinarith [sq_nonneg x]

lemma psi_pos {x : ℝ} (hx : |x| < 1) : 0 < psi x :=
  Real.rpow_pos_of_pos (base_pos hx) _

lemma psi_cube {x : ℝ} (hx : |x| < 1) : psi x ^ 3 = 1-x^2 := by
  rw [psi, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt (base_pos hx))]
  norm_num

lemma psi_le_one {x : ℝ} (hx : |x| < 1) : psi x ≤ 1 := by
  have hp := psi_pos hx
  have hc := psi_cube hx
  nlinarith [sq_nonneg x, sq_nonneg (psi x - 1)]

end
end CurrentKS.Scalar

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_RealificationSPD
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W08

open Matrix
open scoped ComplexOrder BigOperators

theorem realify_conjTranspose {m n : Type*} (A : Matrix m n ℂ) :
    realify Aᴴ = (realify A)ᵀ := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [realify, Matrix.fromBlocks, Matrix.conjTranspose_apply, Matrix.transpose_apply]

theorem realify_isHermitian {n : Type*} (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    (realify A).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have h := congrFun (congrFun (realify_conjTranspose A) j) i
  rw [hA] at h
  simpa using h

theorem realifyVector_dotProduct {n : Type*} [Fintype n] (x y : n → ℂ) :
    realifyVector x ⬝ᵥ realifyVector y = (star x ⬝ᵥ y).re := by
  simp [realifyVector, dotProduct, Fintype.sum_sum_type, Complex.mul_re,
    Finset.sum_add_distrib]

end KS.W08

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_Pivot
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Matrix

namespace KS.W07

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K]

section TrivialStar

variable [StarRing K] [TrivialStar K]

omit [Fintype n] [DecidableEq n] in
theorem pivot_schur_formula {a : K} (ha : a ≠ 0)
    (b : n → K) (D : Matrix n n K) :
    D - (pivotRow b)ᴴ * (scalarPivot a)⁻¹ *
      (pivotRow b) = pivotSchur a b D := by
  ext i j
  simp [scalarPivot_inv ha, scalarPivot, pivotRow, Matrix.mul_apply, pivotSchur]
  ring

omit [DecidableEq n] [StarRing K] [TrivialStar K] in
theorem pivot_lift_cancel {a : K} (ha : a ≠ 0) (b y : n → K) :
    (fun _ : Unit => -(a⁻¹ * ∑ j, b j * y j)) +
      ((scalarPivot a)⁻¹ * (pivotRow b)) *ᵥ y = 0 := by
  ext u
  cases u
  simp [scalarPivot_inv ha, scalarPivot, pivotRow, Matrix.mul_apply, Matrix.mulVec,
    dotProduct, Finset.mul_sum, mul_assoc]

omit [DecidableEq n] in
theorem pivotWitnessLift_quadratic {a : K} (ha : a ≠ 0)
    (b y : n → K) (D : Matrix n n K) :
    pivotWitnessLift a b y ⬝ᵥ (pivotBlock a b D *ᵥ pivotWitnessLift a b y) =
      y ⬝ᵥ (pivotSchur a b D *ᵥ y) := by
  let := scalarPivotInvertible ha
  have hA : (scalarPivot a).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp [scalarPivot]
  have h := Matrix.schur_complement_eq₁₁
    (pivotRow b) D
    (fun _ : Unit => -(a⁻¹ * ∑ j, b j * y j)) y hA
  rw [pivot_lift_cancel ha, pivot_schur_formula ha] at h
  have hblock : Matrix.fromBlocks (scalarPivot a) (pivotRow b) (pivotRow b)ᴴ D =
      pivotBlock a b D := by
    ext i j
    cases i <;> cases j <;> simp [pivotBlock, pivotRow, Matrix.fromBlocks]
  rw [hblock] at h
  simpa only [← Matrix.dotProduct_mulVec, star_trivial, Matrix.zero_mulVec,
    zero_dotProduct, zero_add, pivotWitnessLift] using h

end TrivialStar

end KS.W07

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_NegativeWitness
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17

open Matrix

theorem quadratic_single {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) (i : Fin n) :
    Pi.single i 1 ⬝ᵥ (M *ᵥ Pi.single i 1) = M i i := by
  simp [single_dotProduct]

theorem negativeDiagonal_witness {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ)
    (i : Fin n) (hi : M i i < 0) :
    Pi.single i 1 ⬝ᵥ (M *ᵥ Pi.single i 1) < 0 := by
  simpa only [quadratic_single] using hi

theorem quadratic_twoSingle {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ)
    (i j : Fin n) (a b : ℚ) :
    (Pi.single i a + Pi.single j b) ⬝ᵥ (M *ᵥ (Pi.single i a + Pi.single j b)) =
      a * (M i i * a + M i j * b) + b * (M j i * a + M j j * b) := by
  simp only [add_dotProduct, single_dotProduct, Matrix.mulVec,
    dotProduct_add, dotProduct_single]

theorem zeroPivotWitness_value {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ)
    (i j : Fin n) (hii : M i i = 0) (hij : M i j ≠ 0)
    (hsymm : M j i = M i j) :
    zeroPivotWitness M i j ⬝ᵥ (M *ᵥ zeroPivotWitness M i j) = -1 := by
  unfold zeroPivotWitness
  rw [quadratic_twoSingle, hii, hsymm]
  field_simp [hij]
  ring

theorem zeroPivotWitness_negative {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ)
    (i j : Fin n) (hii : M i i = 0) (hij : M i j ≠ 0)
    (hsymm : M j i = M i j) :
    zeroPivotWitness M i j ⬝ᵥ (M *ᵥ zeroPivotWitness M i j) < 0 := by
  rw [zeroPivotWitness_value M i j hii hij hsymm]
  decide

end KS.W17

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RationalElimination
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17

theorem trailingMatrix_isSymm {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (hM : M.IsSymm) :
    (trailingMatrix M).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  exact hM.apply i.succ j.succ

theorem schurTail_isSymm {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (hM : M.IsSymm) :
    (schurTail M).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [schurTail]
  rw [hM.apply i.succ j.succ, hM.apply 0 j.succ, hM.apply 0 i.succ]
  rw [mul_comm (M 0 j.succ) (M 0 i.succ)]

theorem firstNonzeroOffDiagonal_some {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (j : Fin n)
    (h : firstNonzeroOffDiagonal M = some j) : M 0 j.succ ≠ 0 := by
  have hj := List.find?_some h
  simpa using hj

theorem firstNonzeroOffDiagonal_none_iff {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) :
    firstNonzeroOffDiagonal M = none ↔ ∀ j : Fin n, M 0 j.succ = 0 := by
  simp [firstNonzeroOffDiagonal, List.find?_eq_none]

end KS.W17

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_FinPivot
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Matrix

namespace KS.W07

theorem quadratic_submatrix_equiv {n m K : Type*} [Fintype n] [Fintype m]
    [CommSemiring K] (M : Matrix n n K) (x : n → K) (e : m ≃ n) :
    (x ∘ e) ⬝ᵥ (M.submatrix e e *ᵥ (x ∘ e)) = x ⬝ᵥ (M *ᵥ x) := by
  rw [Matrix.submatrix_mulVec_equiv]
  have hc : (x ∘ e) ∘ e.symm = x := by funext i; simp
  rw [hc]
  exact comp_equiv_dotProduct_comp_equiv x (M *ᵥ x) e

theorem fin_pivotBlock {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (hM : M.IsSymm) :
    M.submatrix (pivotIndexEquiv n) (pivotIndexEquiv n) =
      pivotBlock (M 0 0) (fun i => M 0 i.succ) (KS.W17.trailingMatrix M) := by
  ext i j
  cases i with
  | inl i => cases i; cases j <;> rfl
  | inr i =>
    cases j with
    | inl j => cases j; exact hM.apply 0 i.succ
    | inr j => rfl

theorem fin_pivotSchur {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (hM : M.IsSymm) :
    pivotSchur (M 0 0) (fun i => M 0 i.succ) (KS.W17.trailingMatrix M) =
      KS.W17.schurTail M := by
  ext i j
  simp only [pivotSchur, KS.W17.schurTail, KS.W17.trailingMatrix, hM.apply 0 i.succ]

theorem fin_pivotWitnessLift {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (y : Fin n → ℚ) :
    KS.W17.schurWitnessLift M y ∘ pivotIndexEquiv n =
      pivotWitnessLift (M 0 0) (fun i => M 0 i.succ) y := by
  funext i
  cases i with
  | inl i =>
    cases i
    simp [pivotIndexEquiv, KS.W17.schurWitnessLift,
      pivotWitnessLift, div_eq_mul_inv, mul_comm]
  | inr i => rfl

theorem fin_schurWitnessLift_quadratic {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (hM : M.IsSymm)
    (ha : M 0 0 ≠ 0) (y : Fin n → ℚ) :
    KS.W17.schurWitnessLift M y ⬝ᵥ (M *ᵥ KS.W17.schurWitnessLift M y) =
      y ⬝ᵥ (KS.W17.schurTail M *ᵥ y) := by
  rw [← quadratic_submatrix_equiv M (KS.W17.schurWitnessLift M y) (pivotIndexEquiv n),
    fin_pivotBlock M hM, fin_pivotWitnessLift M y,
    pivotWitnessLift_quadratic ha, fin_pivotSchur M hM]

end KS.W07

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PSDSeparation
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17

open Matrix

theorem psdCutEvalReal_cast {n : ℕ} (q : Fin n → ℚ)
    (M : Matrix (Fin n) (Fin n) ℚ) :
    psdCutEvalReal q (fun i j => (M i j : ℝ)) = (psdCutEval q M : ℝ) := by
  simp [psdCutEvalReal, psdCutEval, dotProduct, Matrix.mulVec,
    Rat.cast_sum, Rat.cast_mul, Rat.cast_neg]

theorem psdCutEvalReal_nonpos {n : ℕ} (q : Fin n → ℚ)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosSemidef) :
    psdCutEvalReal q M ≤ 0 := by
  have h := hM.dotProduct_mulVec_nonneg (fun i => (q i : ℝ))
  simpa [psdCutEvalReal] using neg_nonpos.mpr h

theorem psdWitness_separates {n : ℕ} (q : Fin n → ℚ)
    (M : Matrix (Fin n) (Fin n) ℚ) (hneg : q ⬝ᵥ (M *ᵥ q) < 0) :
    0 < psdCutEvalReal q (fun i j => (M i j : ℝ)) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.PosSemidef → psdCutEvalReal q B ≤ 0 := by
  constructor
  · rw [psdCutEvalReal_cast]
    have hr : 0 < psdCutEval q M := neg_pos.mpr hneg
    exact_mod_cast hr
  · exact fun B hB => psdCutEvalReal_nonpos q B hB

end KS.W17

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_EliminationSoundness
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W17.schurEntryExpr_eval _root_.OAI.KS.W17.schurTail_zero_pivot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17

open Matrix

theorem quadratic_zero_cons {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (y : Fin n → ℚ) :
    Fin.cons 0 y ⬝ᵥ (M *ᵥ Fin.cons 0 y) = y ⬝ᵥ (trailingMatrix M *ᵥ y) := by
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_succ, trailingMatrix]

theorem rationalNegativeWitness_sound (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℚ) (hM : M.IsSymm) (q : Fin n → ℚ)
    (hout : rationalNegativeWitness n M = some q) : q ⬝ᵥ (M *ᵥ q) < 0 := by
  induction n with
  | zero => simp [rationalNegativeWitness] at hout
  | succ n ih =>
      by_cases hnegative : M 0 0 < 0
      · have hq : Pi.single 0 1 = q := by
          simpa [rationalNegativeWitness, hnegative] using hout
        subst q
        exact negativeDiagonal_witness M 0 hnegative
      · by_cases hzero : M 0 0 = 0
        · cases hfind : firstNonzeroOffDiagonal M with
          | some j =>
              have hq : zeroPivotWitness M 0 j.succ = q := by
                simpa [rationalNegativeWitness, hnegative, hzero, hfind] using hout
              subst q
              exact zeroPivotWitness_negative M 0 j.succ hzero
                (firstNonzeroOffDiagonal_some M j hfind) (hM.apply 0 j.succ)
          | none =>
              cases hrec : rationalNegativeWitness n (trailingMatrix M) with
              | none =>
                  simp [rationalNegativeWitness, hzero, hfind, hrec] at hout
              | some y =>
                  have hq : Fin.cons 0 y = q := by
                    simpa [rationalNegativeWitness, hnegative, hzero, hfind, hrec] using hout
                  subst q
                  rw [quadratic_zero_cons]
                  exact ih (trailingMatrix M) (trailingMatrix_isSymm M hM) y hrec
        · cases hrec : rationalNegativeWitness n (schurTail M) with
          | none =>
              simp [rationalNegativeWitness, hnegative, hzero, hrec] at hout
          | some y =>
              have hq : schurWitnessLift M y = q := by
                simpa [rationalNegativeWitness, hnegative, hzero, hrec] using hout
              subst q
              rw [KS.W07.fin_schurWitnessLift_quadratic M hM hzero y]
              exact ih (schurTail M) (schurTail_isSymm M hM) y hrec

theorem computedPSDSeparator_separates (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℚ) (hM : M.IsSymm) (q : Fin n → ℚ)
    (hout : rationalNegativeWitness n M = some q) :
    0 < psdCutEvalReal q (fun i j => (M i j : ℝ)) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.PosSemidef → psdCutEvalReal q B ≤ 0 :=
  psdWitness_separates q M (rationalNegativeWitness_sound n M hM q hout)

end KS.W17

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotPSD
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07

open Matrix

variable {n : Type*} [Fintype n]

theorem scalarPivot_posDef {a : ℝ} (ha : 0 < a) : (scalarPivot a).PosDef := by
  have heq : scalarPivot a = Matrix.diagonal (fun _ : Unit => a) := by
    ext i j
    cases i; cases j
    simp [scalarPivot]
  rw [heq]
  exact Matrix.PosDef.diagonal (fun _ => ha)

omit [Fintype n] in
theorem real_pivot_schur_formula {a : ℝ} (ha : a ≠ 0)
    (b : n → ℝ) (D : Matrix n n ℝ) :
    D - (pivotRow b)ᴴ * (scalarPivot a)⁻¹ *
      (pivotRow b) = pivotSchur a b D :=
  pivot_schur_formula ha b D

theorem pivotSchur_posSemidef {a : ℝ} (ha : 0 < a)
    (b : n → ℝ) (D : Matrix n n ℝ) (hM : (pivotBlock a b D).PosSemidef) :
    (pivotSchur a b D).PosSemidef := by
  let _ := scalarPivotInvertible (ne_of_gt ha)
  have hM' : (Matrix.fromBlocks (scalarPivot a)
      (pivotRow b)
      (pivotRow b)ᴴ D).PosSemidef := by
    exact hM
  have h := (Matrix.PosDef.fromBlocks₁₁
    (pivotRow b) D (scalarPivot_posDef ha)).mp hM'
  exact real_pivot_schur_formula (ne_of_gt ha) b D ▸ h

omit [Fintype n] in
theorem rat_pivotSchur_cast (a : ℚ) (b : n → ℚ) (D : Matrix n n ℚ) :
    (pivotSchur a b D).map (fun q : ℚ => (q : ℝ)) =
      pivotSchur (a : ℝ) (fun i => (b i : ℝ)) (D.map (fun q : ℚ => (q : ℝ))) := by
  ext i j
  simp [pivotSchur]

omit [Fintype n] in
theorem rat_pivotBlock_cast (a : ℚ) (b : n → ℚ) (D : Matrix n n ℚ) :
    (pivotBlock a b D).map (fun q : ℚ => (q : ℝ)) =
      pivotBlock (a : ℝ) (fun i => (b i : ℝ)) (D.map (fun q : ℚ => (q : ℝ))) := by
  ext i j
  cases i <;> cases j <;> rfl

theorem pivotBlock_posSemidef_iff {a : ℝ} (ha : 0 < a)
    (b : n → ℝ) (D : Matrix n n ℝ) :
    (pivotBlock a b D).PosSemidef ↔ (pivotSchur a b D).PosSemidef := by
  constructor
  · exact pivotSchur_posSemidef ha b D
  · intro hS
    let _ := scalarPivotInvertible (ne_of_gt ha)
    have hS' : (D - (pivotRow b)ᴴ * (scalarPivot a)⁻¹ *
        (pivotRow b)).PosSemidef := by
      rwa [real_pivot_schur_formula (ne_of_gt ha)]
    have h := (Matrix.PosDef.fromBlocks₁₁
      (pivotRow b) D (scalarPivot_posDef ha)).mpr hS'
    exact h

theorem zero_pivotBlock_posSemidef (D : Matrix n n ℝ) (hD : D.PosSemidef) :
    (pivotBlock 0 (fun _ => 0) D).PosSemidef := by
  change (Matrix.fromBlocks (0 : Matrix Unit Unit ℝ) 0 0 D).PosSemidef
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · exact Matrix.IsHermitian.fromBlocks Matrix.isHermitian_zero (by simp) hD.isHermitian
  · intro x
    have hx : Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr) = x := Sum.elim_comp_inl_inr x
    have h := hD.dotProduct_mulVec_nonneg (x ∘ Sum.inr)
    rw [← hx]
    simpa [Matrix.fromBlocks_mulVec, Function.comp_def] using h

end KS.W07

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_FinPivotPSD
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07

theorem fin_psd_of_schurTail {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (hM : M.IsSymm)
    (ha : 0 < M 0 0)
    (hS : ((KS.W17.schurTail M).map (fun q : ℚ => (q : ℝ))).PosSemidef) :
    (M.map (fun q : ℚ => (q : ℝ))).PosSemidef := by
  apply (Matrix.posSemidef_submatrix_equiv (pivotIndexEquiv n)).mp
  change ((M.submatrix (pivotIndexEquiv n) (pivotIndexEquiv n)).map
    (fun q : ℚ => (q : ℝ))).PosSemidef
  rw [fin_pivotBlock M hM, rat_pivotBlock_cast]
  apply (pivotBlock_posSemidef_iff (by exact_mod_cast ha) _ _).mpr
  rw [← rat_pivotSchur_cast, fin_pivotSchur M hM]
  exact hS

theorem fin_psd_of_zero_pivot_tail {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (hM : M.IsSymm)
    (ha : M 0 0 = 0) (hrow : ∀ j : Fin n, M 0 j.succ = 0)
    (hD : ((KS.W17.trailingMatrix M).map (fun q : ℚ => (q : ℝ))).PosSemidef) :
    (M.map (fun q : ℚ => (q : ℝ))).PosSemidef := by
  apply (Matrix.posSemidef_submatrix_equiv (pivotIndexEquiv n)).mp
  change ((M.submatrix (pivotIndexEquiv n) (pivotIndexEquiv n)).map
    (fun q : ℚ => (q : ℝ))).PosSemidef
  rw [fin_pivotBlock M hM, rat_pivotBlock_cast]
  simp only [ha, hrow, Rat.cast_zero]
  exact zero_pivotBlock_posSemidef _ hD

end KS.W07

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_EliminationCompleteness
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W17.schurEntryExpr_eval _root_.OAI.KS.W17.schurTail_zero_pivot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17

open Matrix

theorem rationalNegativeWitness_none_psd (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℚ) (hM : M.IsSymm)
    (hout : rationalNegativeWitness n M = none) :
    (M.map (fun q : ℚ => (q : ℝ))).PosSemidef := by
  induction n with
  | zero =>
      have hz : M.map (fun q : ℚ => (q : ℝ)) = 0 := by
        ext i j
        exact Fin.elim0 i
      rw [hz]
      exact Matrix.PosSemidef.zero
  | succ n ih =>
      by_cases hnegative : M 0 0 < 0
      · simp [rationalNegativeWitness, hnegative] at hout
      · by_cases hzero : M 0 0 = 0
        · cases hfind : firstNonzeroOffDiagonal M with
          | some j =>
              simp [rationalNegativeWitness, hzero, hfind] at hout
          | none =>
              have hrec : rationalNegativeWitness n (trailingMatrix M) = none := by
                simpa [rationalNegativeWitness, hnegative, hzero, hfind] using hout
              exact KS.W07.fin_psd_of_zero_pivot_tail M hM hzero
                ((firstNonzeroOffDiagonal_none_iff M).mp hfind)
                (ih (trailingMatrix M) (trailingMatrix_isSymm M hM) hrec)
        · have hrec : rationalNegativeWitness n (schurTail M) = none := by
            simpa [rationalNegativeWitness, hnegative, hzero] using hout
          have ha : 0 < M 0 0 :=
            lt_of_le_of_ne (le_of_not_gt hnegative) (Ne.symm hzero)
          exact KS.W07.fin_psd_of_schurTail M hM ha
            (ih (schurTail M) (schurTail_isSymm M hM) hrec)

end KS.W17

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_HermitianMat
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.invH_val _root_.OAI.CurrentKS.Hermitian.matrixTraceCLM_apply _root_.OAI.CurrentKS.Hermitian.realTrace_add _root_.OAI.CurrentKS.Hermitian.realTrace_one _root_.OAI.CurrentKS.Hermitian.realTrace_smul _root_.OAI.CurrentKS.Hermitian.realTrace_sub _root_.OAI.CurrentKS.Hermitian.realTrace_zero _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Hermitian.sandwichCLM_apply _root_.OAI.CurrentKS.Hermitian.sandwich_val _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply _root_.OAI.CurrentKS.Variational.mem_pairCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder InnerProductSpace

variable {d : ℕ}

section OperatorNorm
open scoped Matrix.Norms.L2Operator MatrixOrder

theorem trace_mul_nonneg {A B : Mat d} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace.re := by
  let : CStarAlgebra (Mat d) := {}
  have hs : (CFC.sqrt A).PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  have ht := (hB.mul_mul_conjTranspose_same (CFC.sqrt A)).trace_nonneg
  rw [hs.isHermitian.eq, Matrix.trace_mul_cycle,
    CFC.sqrt_mul_sqrt_self A hA.nonneg] at ht
  exact (Complex.nonneg_iff.mp ht).1

end OperatorNorm

open scoped Matrix.Norms.Frobenius

lemma inner_smul_leftH (A B : H d) (r : ℝ) :
    inner ℝ (r • A) B = r * inner ℝ A B := by
  exact real_inner_smul_left A B r

theorem matrix_inner (d : ℕ) (A B : Mat d) :
    inner ℂ A B = (B * Aᴴ).trace := by
  change inner ℂ (asL2 A) (asL2 B) = _
  simp only [asL2, PiLp.inner_apply, RCLike.inner_apply,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  congr 1

theorem inner_eq_trace (A B : H d) :
    inner ℝ A B = ((A : Mat d) * (B : Mat d)).trace.re := by
  change (inner ℂ (A : Mat d) (B : Mat d)).re = _
  rw [matrix_inner, A.property.eq, Matrix.trace_mul_comm]

@[simp] theorem inner_one (A : H d) : inner ℝ one A = realTrace A := by
  rw [inner_eq_trace, one_val, one_mul]
  rfl

@[simp] theorem inner_one' (A : H d) : inner ℝ A one = realTrace A := by
  rw [real_inner_comm]
  exact inner_one A

theorem inner_nonneg_of_psd (A B : H d) (hA : A ∈ psdCone d) (hB : B ∈ psdCone d) :
    0 ≤ inner ℝ A B := by
  rw [inner_eq_trace]
  exact trace_mul_nonneg hA hB

theorem rankOne_mem_psdCone (v : Fin d → ℂ) : rankOne v ∈ psdCone d :=
  Matrix.posSemidef_vecMulVec_self_star v

theorem inner_rankOne (A : H d) (v : Fin d → ℂ) :
    inner ℝ A (rankOne v) = (star v ⬝ᵥ ((A : Mat d) *ᵥ v)).re := by
  rw [inner_eq_trace]
  change ((A : Mat d) * Matrix.vecMulVec v (star v)).trace.re = _
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

theorem psd_of_inner_nonneg (A : H d)
    (h : ∀ B ∈ psdCone d, 0 ≤ inner ℝ A B) : A ∈ psdCone d := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨A.property, fun v => ?_⟩
  apply Complex.nonneg_iff.mpr
  refine ⟨?_, ?_⟩
  · simpa only [inner_rankOne] using h (rankOne v) (rankOne_mem_psdCone v)
  · exact (A.property.im_star_dotProduct_mulVec_self v).symm

theorem isClosed_psdCone : IsClosed (psdCone d : Set (H d)) := by
  have he : (psdCone d : Set (H d)) =
      {A : H d | ∀ v : Fin d → ℂ, 0 ≤ (star v ⬝ᵥ ((A : Mat d) *ᵥ v)).re} := by
    ext A
    constructor
    · intro hA v
      exact hA.re_dotProduct_nonneg v
    · intro hA
      apply psd_of_inner_nonneg A

      have hp : (A : Mat d).PosSemidef :=
        Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨A.property, fun v =>
          Complex.nonneg_iff.mpr ⟨hA v, (A.property.im_star_dotProduct_mulVec_self v).symm⟩⟩
      exact fun B hB => inner_nonneg_of_psd A B hp hB
  rw [he]
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro v
  apply isClosed_le continuous_const
  exact Complex.continuous_re.comp (continuous_const.dotProduct
    (continuous_subtype_val.matrix_mulVec continuous_const))

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_InvH
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.matrixTraceCLM_apply _root_.OAI.CurrentKS.Hermitian.realTrace_add _root_.OAI.CurrentKS.Hermitian.realTrace_smul _root_.OAI.CurrentKS.Hermitian.realTrace_sub _root_.OAI.CurrentKS.Hermitian.realTrace_zero _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Hermitian.sandwichCLM_apply _root_.OAI.CurrentKS.Hermitian.sandwich_val _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply _root_.OAI.CurrentKS.Variational.mem_pairCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder

variable {d : ℕ}

lemma pd_smul {A : H d} (hA : A ∈ pd d) {a : ℝ} (ha : 0 < a) :
    a • A ∈ pd d := by
  change ((a : ℂ) • (A : Mat d)).PosDef
  exact hA.smul (by exact_mod_cast ha)

lemma isClosed_lowerBound (a : ℝ) :
    IsClosed {A : H d | (a • one : H d) ≤ A} := by
  change IsClosed ((fun A : H d => A - a • one) ⁻¹' (psdCone d : Set (H d)))
  exact (isClosed_psdCone (d := d)).preimage (continuous_id.sub continuous_const)

lemma isClosed_upperBound (b : ℝ) :
    IsClosed {A : H d | A ≤ (b • one : H d)} := by
  change IsClosed ((fun A : H d => b • one - A) ⁻¹' (psdCone d : Set (H d)))
  exact (isClosed_psdCone (d := d)).preimage (continuous_const.sub continuous_id)

lemma isClosed_orderBox (a b : ℝ) :
    IsClosed {A : H d | (a • one : H d) ≤ A ∧ A ≤ b • one} :=
  (isClosed_lowerBound a).inter (isClosed_upperBound b)

open scoped Matrix.Norms.L2Operator

theorem inverse_antitone {A B : Mat d} (hA : A.PosDef) (hB : B.PosDef) (hab : A ≤ B) :
    B⁻¹ ≤ A⁻¹ := by
  let : CStarAlgebra (Mat d) := {}
  obtain ⟨u, rfl⟩ := hA.isUnit
  obtain ⟨v, rfl⟩ := hB.isUnit
  simpa only [Matrix.coe_units_inv] using CStarAlgebra.inv_le_inv hA.posSemidef.nonneg hab

lemma scalar_posDef {a : ℝ} (ha : 0 < a) : ((a : ℂ) • (1 : Mat d)).PosDef :=
  Matrix.PosDef.one.smul (by exact_mod_cast ha)

lemma scalar_inv (a : ℝ) : (((a : ℂ) • (1 : Mat d))⁻¹) = (a⁻¹ : ℂ) • (1 : Mat d) := by
  by_cases ha : a = 0
  · simp [ha]
  · let : Invertible (a : ℂ) := invertibleOfNonzero (by exact_mod_cast ha)
    rw [Matrix.inv_smul _ _ (by simp), invOf_eq_inv]
    simp

theorem le_trace_smul_one {A : Mat d} (hA : A.PosSemidef) :
    A ≤ (A.trace.re : ℂ) • (1 : Mat d) := by
  let : CStarAlgebra (Mat d) := {}
  have heig (i : Fin d) : hA.isHermitian.eigenvalues i ≤ A.trace.re := by
    rw [hA.isHermitian.trace_eq_sum_eigenvalues, Complex.re_sum]
    exact Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)
  have hc : 0 ≤ cfc (fun x : ℝ => A.trace.re - x) A := by
    apply (cfc_nonneg_iff _ A).mpr
    intro x hx
    obtain ⟨i, rfl⟩ := hA.isHermitian.spectrum_real_eq_range_eigenvalues ▸ hx
    exact sub_nonneg.mpr (heig i)
  rw [cfc_sub (fun _ : ℝ => A.trace.re) (fun x : ℝ => x),
    cfc_const _ A hA.isHermitian.isSelfAdjoint] at hc
  change 0 ≤ (algebraMap ℝ (Mat d)) A.trace.re - cfc (id : ℝ → ℝ) A at hc
  rw [cfc_id ℝ A hA.isHermitian.isSelfAdjoint] at hc
  have hmap : (algebraMap ℝ (Mat d)) A.trace.re = (A.trace.re : ℂ) • (1 : Mat d) := by
    ext i j
    simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply, Matrix.smul_apply,
      Matrix.one_apply]
  rw [hmap] at hc
  exact sub_nonneg.mp hc

theorem isCompact_orderBox (a b : ℝ) :
    IsCompact {A : H d | (a • one : H d) ≤ A ∧ A ≤ b • one} := by
  let : CStarAlgebra (Mat d) := {}
  let : ProperSpace (H d) := FiniteDimensional.proper ℝ (H d)
  apply (isCompact_closedBall (a • one : H d) ‖(b-a) • (one : H d)‖).of_isClosed_subset
    (isClosed_orderBox a b)
  intro A hA
  rw [Metric.mem_closedBall]
  change dist (A : Mat d) (a • (1 : Mat d)) ≤ ‖(b-a) • (1 : Mat d)‖
  rw [dist_eq_norm]
  have h₁ : a • (1 : Mat d) ≤ (A : Mat d) := hA.1
  have h₂ : (A : Mat d) ≤ b • (1 : Mat d) := hA.2
  apply CStarAlgebra.norm_le_norm_of_le_of_nonneg _ (sub_nonneg.mpr h₁)
  have hh := sub_le_sub_right h₂ (a • (1 : Mat d))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul,
    Complex.ofReal_sub]
  ring

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_Sandwich
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Hermitian

section L2Operator

open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {d : ℕ}

lemma sandwich_psd (A U : H d) (hU : U ∈ psdCone d) : sandwich A U ∈ psdCone d := by
  have hh := hU.mul_mul_conjTranspose_same (A : Mat d)
  rw [A.property.eq] at hh
  exact hh

end L2Operator

section Frobenius

open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma inner_sandwich (A U P : H d) :
    inner ℝ P (sandwich A U) = inner ℝ (sandwich A P) U := by
  rw [inner_eq_trace, inner_eq_trace]
  change ((P : Mat d) * ((A : Mat d) * (U : Mat d) * (A : Mat d))).trace.re =
    ((A : Mat d) * (P : Mat d) * (A : Mat d) * (U : Mat d)).trace.re
  rw [← mul_assoc, ← mul_assoc, Matrix.trace_mul_comm ((P : Mat d) * (A : Mat d) * (U : Mat d))]
  simp only [mul_assoc]

end Frobenius

end CurrentKS.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_TraceCLM
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.matrixTraceCLM_apply _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Hermitian.sandwichCLM_apply _root_.OAI.CurrentKS.Hermitian.sandwich_val _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply _root_.OAI.CurrentKS.Variational.mem_pairCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma realTrace_nonneg {A : H d} (hA : A ∈ psdCone d) : 0 ≤ realTrace A :=
  (Complex.nonneg_iff.mp hA.trace_nonneg).1

lemma realTrace_mono {A B : H d} (hab : A ≤ B) : realTrace A ≤ realTrace B := by
  have hh := realTrace_nonneg (show B-A ∈ psdCone d from hab)
  simpa using hh

@[simp] lemma traceCLM_apply (A : H d) : traceCLM A = realTrace A := inner_one A

lemma continuous_realTrace : Continuous (realTrace : H d → ℝ) := by
  have he : (fun A : H d => traceCLM A) = realTrace := funext traceCLM_apply
  rw [← he]
  exact (traceCLM (d := d)).continuous

lemma continuousAt_invH {A : H d} (hA : A ∈ pd d) : ContinuousAt invH A := by
  have hm : ContinuousAt (Inv.inv : Mat d → Mat d) (A : Mat d) := by
    apply continuousAt_matrix_inv
    have he : (Ring.inverse : ℂ → ℂ) = Inv.inv := funext Ring.inverse_eq_inv
    rw [he]
    exact continuousAt_inv₀ hA.det_pos.ne'
  apply tendsto_subtype_rng.mpr
  exact hm.comp continuousAt_subtype_val

lemma pd_of_lower {a : ℝ} (ha : 0 < a) {A : H d} (hA : a • one ≤ A) : A ∈ pd d := by
  have hp : ((A : Mat d) - (a : ℂ) • 1).PosSemidef := hA
  have hs := (scalar_posDef ha).add_posSemidef hp
  simp only [add_sub_cancel] at hs
  exact hs

lemma inverse_bound_below {a : ℝ} (ha : 0 < a) {A : H d}
    (hA : A ∈ pd d) (he : invH A ≤ a • one) : a⁻¹ • one ≤ A := by
  let : Invertible (A : Mat d) := hA.isUnit.invertible
  have hi := inverse_antitone hA.inv (scalar_posDef ha) he
  rw [scalar_inv, Matrix.inv_inv_of_invertible] at hi
  change ((a⁻¹ : ℝ) : ℂ) • (1 : Mat d) ≤ (A : Mat d)
  simpa only [Complex.ofReal_inv] using hi

lemma psd_nonneg {A : H d} (hA : A ∈ psdCone d) : 0 ≤ A := hA.nonneg

lemma mem_psd_iff_nonneg (A : H d) : A ∈ psdCone d ↔ 0 ≤ A := by
  constructor
  · exact psd_nonneg
  · intro hA
    have hh : (0 : Mat d) ≤ (A : Mat d) := hA
    exact hh.posSemidef

lemma scalar_one_mono {r s : ℝ} (hrs : r ≤ s) :
    r • (one : H d) ≤ s • one := by
  apply sub_nonneg.mp
  erw [← sub_smul]
  exact psd_nonneg (psd_smul one_mem_psdCone (sub_nonneg.mpr hrs))

lemma trace_bound_above {A : H d} (hA : A ∈ psdCone d) : A ≤ realTrace A • one :=
  le_trace_smul_one hA

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_InnerRight
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma trace_zero_psd {A : H d} (hA : A ∈ psdCone d) (htr : realTrace A = 0) : A = 0 := by
  apply le_antisymm
  · simpa only [htr, zero_smul] using trace_bound_above hA
  · exact psd_nonneg hA

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_OperatorNorm
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Hermitian

section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {d : ℕ}

lemma operatorNorm_nonneg (A : H d) : 0 ≤ operatorNorm A := norm_nonneg _

lemma operatorNorm_eq_matrix (A : H d) : operatorNorm A = ‖(A : Mat d)‖ := rfl

lemma scalarOne_eq_algebraMap (r : ℝ) : ((r • (one : H d) : H d) : Mat d) = algebraMap ℝ (Mat d) r := by
  rw [Algebra.algebraMap_eq_smul_one]
  rfl

lemma operatorNorm_le_of_bounds {A : H d} {r : ℝ} (hr : 0 ≤ r)
    (hlo : -r • (one : H d) ≤ A) (hhi : A ≤ r • (one : H d)) : operatorNorm A ≤ r := by
  let : CStarAlgebra (Mat d) := {}
  by_cases htriv : Subsingleton (Mat d)
  · let := htriv
    rw [operatorNorm_eq_matrix,Subsingleton.elim (A : Mat d) 0,norm_zero]
    exact hr
  · have : Nontrivial (Mat d) := not_subsingleton_iff_nontrivial.mp htriv
    have hh : (A : Mat d) ≤ algebraMap ℝ (Mat d) r := by
      change (A : Mat d) ≤ ((r • one : H d) : Mat d) at hhi
      rwa [scalarOne_eq_algebraMap] at hhi
    have hl : algebraMap ℝ (Mat d) (-r) ≤ (A : Mat d) := by
      change ((-r • one : H d) : Mat d) ≤ (A : Mat d) at hlo
      rwa [scalarOne_eq_algebraMap] at hlo
    rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum (a := (A : Mat d)) A.property.isSelfAdjoint with hn | hn
    · exact (le_algebraMap_iff_spectrum_le A.property.isSelfAdjoint).mp hh _ hn
    · have h := (algebraMap_le_iff_le_spectrum A.property.isSelfAdjoint).mp hl _ hn
      change ‖(A : Mat d)‖ ≤ r
      linarith

lemma le_operatorNorm_smul_one (A : H d) : A ≤ operatorNorm A • one := by
  let : CStarAlgebra (Mat d) := {}
  change (A : Mat d) ≤ ((operatorNorm A • one : H d) : Mat d)
  rw [scalarOne_eq_algebraMap,operatorNorm_eq_matrix]
  exact A.property.isSelfAdjoint.le_algebraMap_norm_self

lemma operatorNorm_le_of_psd_le {A : H d} (hA : A ∈ psdCone d) {r : ℝ} (hr : 0 ≤ r)
    (hhi : A ≤ r • (one : H d)) : operatorNorm A ≤ r := by
  let : CStarAlgebra (Mat d) := {}
  apply (CStarAlgebra.norm_le_iff_le_algebraMap (A : Mat d) hr hA.nonneg).mpr
  change (A : Mat d) ≤ ((r • one : H d) : Mat d) at hhi
  rwa [scalarOne_eq_algebraMap] at hhi

lemma operatorNorm_eq_zero_iff (A : H d) : operatorNorm A = 0 ↔ A = 0 := by
  rw [operatorNorm_eq_matrix,norm_eq_zero]
  exact ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩

lemma operatorNorm_smul (r : ℝ) (A : H d) : operatorNorm (r • A) = |r| * operatorNorm A := by
  change ‖(r : ℂ) • (A : Mat d)‖ = _
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
  rfl

end

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

end CurrentKS.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_OperatorNormSquare
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

variable {d N : ℕ}

lemma operatorNorm_square (A : H d) :
    operatorNorm (sandwich A (one : H d))=(operatorNorm A)^2 := by
  let : CStarAlgebra (Mat d) := {}
  have he := A.property.isSelfAdjoint.norm_mul_self
  simpa only [operatorNorm_eq_matrix,sandwich_val,one_val,mul_one] using he

lemma atom_operatorNorm_le_sqrt (A : Fin N → H d) {ν : ℝ} (hν : 0≤ν)
    (hvar : (∑ i,sandwich (A i) (one : H d))≤ν • (one : H d)) (i : Fin N) :
    operatorNorm (A i)≤Real.sqrt ν := by
  have hle : sandwich (A i) (one : H d)≤ν • (one : H d) :=
    (Finset.single_le_sum (fun j _ => psd_nonneg (sandwich_psd (A j) _ one_mem_psdCone))
      (Finset.mem_univ i)).trans hvar
  have hn := operatorNorm_le_of_psd_le (sandwich_psd (A i) _ one_mem_psdCone) hν hle
  rw [operatorNorm_square] at hn
  exact (Real.le_sqrt (operatorNorm_nonneg _) hν).mpr hn

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PosLower
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Hermitian.sandwichCLM_apply _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply _root_.OAI.CurrentKS.Variational.mem_pairCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Hermitian

section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {d : ℕ}

lemma exists_pos_lower [NeZero d] {P : H d} (hP : P ∈ pd d) :
    ∃ a : ℝ, 0 < a ∧ a • (one : H d) ≤ P := by
  let : CStarAlgebra (Mat d) := {}
  obtain ⟨a, ha, hap⟩ := (CFC.exists_pos_algebraMap_le_iff (a := (P : Mat d)) P.property).mpr
    ((StarOrderedRing.isStrictlyPositive_iff_spectrum_pos (P : Mat d)).mp hP.isStrictlyPositive)
  refine ⟨a, ha, ?_⟩
  change (a : ℂ) • (1 : Mat d) ≤ (P : Mat d)
  convert hap using 1
  all_goals try with_reducible_and_instances rfl
  ext i j
  simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply, Matrix.smul_apply,
    Matrix.one_apply]

end

open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma eq_zero_of_inner_pd [NeZero d] {P Z : H d} (hP : P ∈ pd d)
    (hZ : Z ∈ psdCone d) (hz : inner ℝ P Z = 0) : Z = 0 := by
  obtain ⟨a, ha, hap⟩ := exists_pos_lower hP
  have hh := inner_nonneg_of_psd (P-a•one) Z (show P-a•one ∈ psdCone d from hap) hZ
  rw [inner_sub_left, inner_smul_leftH, inner_one, hz] at hh
  have htr := realTrace_nonneg hZ
  apply trace_zero_psd hZ
  nlinarith

end CurrentKS.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RealTrace
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS
noncomputable section
open scoped BigOperators ComplexOrder

variable {d : ℕ}

theorem nonzero_eigenvalues_card_le (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) :
    Fintype.card {i // hA.eigenvalues i ≠ 0} ≤ A.rank := by
  classical
  have h := hA.conjStarAlgAut_star_eigenvectorUnitary
  have hr : (Matrix.diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ hA.eigenvalues)).rank
      ≤ A.rank := by
    rw [← h]
    simp only [Unitary.conjStarAlgAut_apply]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  rw [Matrix.rank_diagonal] at hr
  simpa only [Function.comp_apply, ne_eq, RCLike.ofReal_eq_zero] using hr

theorem nonzero_eigenvalue_unique (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (hrank : A.rank ≤ 1)
    (i j : Fin d) (hi : hA.eigenvalues i ≠ 0) (hj : hA.eigenvalues j ≠ 0) :
    i = j := by
  have hcard : Fintype.card {i // hA.eigenvalues i ≠ 0} ≤ 1 :=
    (nonzero_eigenvalues_card_le A hA).trans hrank
  have hs := Fintype.card_le_one_iff_subsingleton.mp hcard
  exact congrArg Subtype.val (hs.elim (⟨i, hi⟩ : {i // hA.eigenvalues i ≠ 0}) ⟨j, hj⟩)

end
end CurrentKS

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RankFactor
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder

variable {d : ℕ}

lemma rank_one_factor (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.PosSemidef)
    (hrank : A.rank ≤ 1) : ∃ u : Fin d → ℂ, A = vecMulVec u (star u) := by
  classical
  by_cases hzero : A = 0
  · refine ⟨0, ?_⟩
    rw [hzero]
    ext j k
    simp [vecMulVec]
  have he : ∃ i, hA.isHermitian.eigenvalues i ≠ 0 := by
    by_contra! hh
    apply hzero
    exact hA.isHermitian.eigenvalues_eq_zero_iff.mp (funext hh)
  obtain ⟨i,hi⟩ := he
  let U : Matrix (Fin d) (Fin d) ℂ := hA.isHermitian.eigenvectorUnitary
  let e : ℝ := hA.isHermitian.eigenvalues i
  have he0 : 0 ≤ e := hA.eigenvalues_nonneg i
  have hsqrt : (Real.sqrt e : ℂ) * (Real.sqrt e : ℂ) = (e : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt he0
  refine ⟨fun j => (Real.sqrt e : ℂ) * U j i, ?_⟩
  have hspec := hA.isHermitian.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose] at hspec
  rw [hspec]
  ext j k
  change ∑ l, ((U * diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ hA.isHermitian.eigenvalues)) j l) *
      U.conjTranspose l k = ((Real.sqrt e : ℂ)*U j i) * star ((Real.sqrt e : ℂ)*U k i)
  rw [Finset.sum_eq_single i]
  · simp only [Matrix.mul_diagonal,Function.comp_apply,Matrix.conjTranspose_apply,
      StarMul.star_mul,Complex.star_def,Complex.conj_ofReal]
    change U j i * (e : ℂ) * star (U k i) =
      ((Real.sqrt e : ℂ) * U j i) * (star (U k i) * (Real.sqrt e : ℂ))
    rw [← hsqrt]
    ring
  · intro l _ hli
    have hl : hA.isHermitian.eigenvalues l = 0 := by
      by_contra hl
      exact hli (nonzero_eigenvalue_unique A hA.isHermitian hrank l i hl hi)
    simp only [Matrix.mul_diagonal,Function.comp_apply,hl,RCLike.ofReal_zero,mul_zero,zero_mul]
  · simp

lemma outer_sandwich (u : Fin d → ℂ) (B : Matrix (Fin d) (Fin d) ℂ) :
    vecMulVec u (star u) * B * vecMulVec u (star u) =
      (star u ⬝ᵥ (B *ᵥ u)) • vecMulVec u (star u) := by
  ext i j
  simp only [Matrix.mul_apply,vecMulVec_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.mulVec,dotProduct]
  simp only [Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma trace_outer_mul (u : Fin d → ℂ) (B : Matrix (Fin d) (Fin d) ℂ) :
    (vecMulVec u (star u) * B).trace = star u ⬝ᵥ (B *ᵥ u) := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,vecMulVec_apply,Matrix.mulVec,dotProduct,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma rank_one_sandwich (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.PosSemidef)
    (hrank : A.rank ≤ 1) (B : Matrix (Fin d) (Fin d) ℂ) :
    A*B*A = (A*B).trace • A := by
  obtain ⟨u,rfl⟩ := rank_one_factor A hA hrank
  rw [outer_sandwich,trace_outer_mul]

end
end CurrentKS

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RationalPSDDecision
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17
open Matrix

theorem rationalNegativeWitness_none_iff_psd (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℚ) (hM : M.IsSymm) :
    rationalNegativeWitness n M = none ↔
      (M.map (fun q : ℚ => (q : ℝ))).PosSemidef := by
  constructor
  · exact rationalNegativeWitness_none_psd n M hM
  · intro hPSD
    cases ho : rationalNegativeWitness n M with
    | none => rfl
    | some q =>
      have hs := computedPSDSeparator_separates n M hM q ho
      have hn := hs.2 (M.map (fun r : ℚ => (r : ℝ))) hPSD
      exact (not_lt_of_ge hn hs.1).elim

end KS.W17

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RealDecode
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.HermitianCoordinates
open Matrix
open scoped BigOperators

variable {d : ℕ}

lemma realDecode_map {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (x : Fin d × Fin d → R) : (realDecode x).map f=realDecode (f ∘ x) := by
  ext i j
  cases i <;> cases j <;>
    simp only [realDecode_inl_inl, realDecode_inl_inr, realDecode_inr_inl, realDecode_inr_inr, Matrix.map_apply,
      Function.comp_def,map_neg]
  all_goals split_ifs <;> simp only [map_neg,map_zero]

lemma realDecode_ratCast (x : Fin d × Fin d → ℚ) :
    (realDecode x).map (fun q => (q:ℝ))=realDecode (fun i => (x i:ℝ)) :=
  realDecode_map (algebraMap ℚ ℝ) x
end CurrentKS.HermitianCoordinates

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RealTraceSum
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma realTrace_sum {ι : Type*} (s : Finset ι) (A : ι → H d) :
    realTrace (∑ i ∈ s, A i) = ∑ i ∈ s, realTrace (A i) := by
  simp only [← inner_one, inner_sum]

lemma psd_sum {ι : Type*} (s : Finset ι) (A : ι → H d) (hA : ∀ i ∈ s, A i ∈ psdCone d) :
    (∑ i ∈ s, A i) ∈ psdCone d := by
  exact (mem_psd_iff_nonneg _).mpr (Finset.sum_nonneg fun i hi => (mem_psd_iff_nonneg _).mp (hA i hi))

lemma smul_order {A B : H d} (h : A ≤ B) {r : ℝ} (hr : 0 ≤ r) : r • A ≤ r • B := by
  apply sub_nonneg.mp
  rw [← smul_sub r B A]
  exact (mem_psd_iff_nonneg _).mp (psd_smul ((mem_psd_iff_nonneg _).mpr (sub_nonneg.mpr h)) hr)

lemma scalar_mono_psd {A : H d} (hA : A ∈ psdCone d) {r s : ℝ} (hrs : r ≤ s) : r • A ≤ s • A := by
  apply sub_nonneg.mp
  rw [← sub_smul s r A]
  exact (mem_psd_iff_nonneg _).mp (psd_smul hA (sub_nonneg.mpr hrs))

lemma invH_scalar (a : ℝ) : invH (a • (Hermitian.one : H d)) = a⁻¹ • (Hermitian.one : H d) := by
  apply Subtype.ext
  change (a • (1 : Mat d))⁻¹ = a⁻¹ • (1 : Mat d)
  have h (r : ℝ) : r • (1 : Mat d) = (r : ℂ) • (1 : Mat d) := by
    ext i j
    exact Complex.real_smul
  rw [h a, h a⁻¹, Complex.ofReal_inv]
  exact scalar_inv a

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RealifyHermitian
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace KS.W08
open Matrix
open scoped ComplexOrder BigOperators

lemma realify_isHermitian_iff {n : Type*} (A : Matrix n n ℂ) :
    (realify A).IsHermitian ↔ A.IsHermitian := by
  refine ⟨?_,realify_isHermitian A⟩
  intro h
  apply realify_injective
  rw [realify_conjTranspose]
  simpa using h.eq

theorem realify_posSemidef_iff {n : Type*} [Fintype n] (A : Matrix n n ℂ) :
    (realify A).PosSemidef ↔ A.PosSemidef := by
  constructor
  · intro h
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ((realify_isHermitian_iff A).mp h.isHermitian) ?_
    intro v
    have hv := h.dotProduct_mulVec_nonneg (realifyVector v)
    rw [star_trivial,← realify_mulVec,realifyVector_dotProduct] at hv
    exact Complex.nonneg_iff.mpr ⟨hv,((realify_isHermitian_iff A).mp h.isHermitian |>.im_star_dotProduct_mulVec_self v).symm⟩
  · intro h
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (realify_isHermitian A h.isHermitian) ?_
    intro v
    have hv := h.dotProduct_mulVec_nonneg (complexifyVector v)
    have hr : 0 ≤ (star (complexifyVector v) ⬝ᵥ (A *ᵥ complexifyVector v)).re :=
      Complex.nonneg_iff.mp hv |>.1
    rw [← realifyVector_dotProduct,realify_mulVec,realifyVector_complexify] at hr
    simpa only [star_trivial] using hr

end KS.W08

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_Sandwich2
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Hermitian.sandwichCLM_apply _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply _root_.OAI.CurrentKS.Variational.mem_pairCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma sandwich_eq_zero_iff [NeZero d] (U B : H d) (hB : B ∈ pd d) :
    sandwich U B = 0 ↔ U = 0 := by
  constructor
  · intro he
    have hz : inner ℝ B (sandwich U Hermitian.one) = 0 := by
      rw [real_inner_comm, ← inner_sandwich, he, inner_zero_right]
    have hs := eq_zero_of_inner_pd hB (sandwich_psd U _ one_mem_psdCone) hz
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [inner_eq_trace]
    have hv : (U : Mat d) * (U : Mat d) = 0 := by
      have hh := congrArg Subtype.val hs
      simpa only [sandwich_val, one_val, mul_one, ZeroMemClass.coe_zero] using hh
    rw [hv]
    simp
  · rintro rfl
    apply Subtype.ext
    simp [sandwich]

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_SandwichShiftInverse
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Hermitian
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma trace_mul_real (A B : H d) : (((A : Mat d)*(B : Mat d)).trace.re : ℂ) = ((A : Mat d)*(B : Mat d)).trace := by
  have hs : star (((A : Mat d)*(B : Mat d)).trace) = ((A : Mat d)*(B : Mat d)).trace := by
    rw [← Matrix.trace_conjTranspose,Matrix.conjTranspose_mul,A.property.eq,B.property.eq,Matrix.trace_mul_comm]
  exact Complex.conj_eq_iff_re.mp hs

lemma sandwich_rank_one (A B : H d) (hA : A ∈ psdCone d) (hrank : (A : Mat d).rank ≤ 1) :
    sandwich A B = (inner ℝ A B) • A := by
  apply Subtype.ext
  change (A : Mat d)*(B : Mat d)*(A : Mat d) = (inner ℝ A B) • (A : Mat d)
  rw [CurrentKS.rank_one_sandwich _ hA hrank,inner_eq_trace]
  have hs (r : ℝ) : r • (A : Mat d) = (r : ℂ) • (A : Mat d) := by
    ext i j
    exact Complex.real_smul
  rw [hs,trace_mul_real]

end CurrentKS.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_AffineRealEval
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open Matrix CurrentKS.HermitianCoordinates
open scoped BigOperators

variable {n m p d N : ℕ}

lemma realFinDecode_cast (x : Fin d × Fin d → ℚ) :
    (realFinDecode d x).map (fun q => (q:ℝ))=realFinDecode d (fun i => (x i:ℝ)) := by
  change ((realDecode x).submatrix _ _).map _=(realDecode _).submatrix _ _
  rw [← Matrix.submatrix_map,realDecode_ratCast]

lemma cast_matrix_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix (Fin m) (Fin m) ℚ) :
    (∑ i ∈ s,A i).map (fun q => (q:ℝ))=∑ i ∈ s,(A i).map (fun q => (q:ℝ)) := by
  ext i j
  simp [Matrix.sum_apply,Rat.cast_sum]
lemma cast_matrix_smul (r : ℚ) (A : Matrix (Fin m) (Fin m) ℚ) :
    (r • A).map (fun q => (q:ℝ))=(r:ℝ) • A.map (fun q => (q:ℝ)) := by
  ext i j
  simp [Matrix.smul_apply]
lemma cast_matrix_one : (1 : Matrix (Fin m) (Fin m) ℚ).map (fun q => (q:ℝ))=1 := by
  exact Matrix.map_one _ (by simp) (by simp)
lemma cast_matrix_sub (A B : Matrix (Fin m) (Fin m) ℚ) :
    (A-B).map (fun q => (q:ℝ))=A.map (fun q => (q:ℝ))-B.map (fun q => (q:ℝ)) := by
  ext i j
  simp
lemma cast_matrix_mul (A B : Matrix (Fin m) (Fin m) ℚ) :
    (A*B).map (fun q => (q:ℝ))=A.map (fun q => (q:ℝ))*B.map (fun q => (q:ℝ)) := by
  exact Matrix.map_mul (f := algebraMap ℚ ℝ)

end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_FinRealify
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open Matrix CurrentKS.HermitianCoordinates KS.W08
open scoped BigOperators ComplexOrder

variable {n m p d N : ℕ}

lemma posSemidef_reindex_iff {α β : Type*} [Fintype α] [Fintype β]
    (A : Matrix α α ℝ) (e : β ≃ α) : (A.submatrix e e).PosSemidef ↔ A.PosSemidef := by
  constructor
  · intro h
    have hh := h.submatrix e.symm
    simp only [Matrix.submatrix_submatrix,Function.comp_def,Equiv.apply_symm_apply] at hh
    exact hh
  · exact fun h => h.submatrix _

lemma finRealify_psd (A : Matrix (Fin d) (Fin d) ℂ) :
    (finRealify A).PosSemidef ↔ A.PosSemidef := by
  rw [finRealify,posSemidef_reindex_iff,realify_posSemidef_iff]
lemma finRealify_one : finRealify (1 : Matrix (Fin d) (Fin d) ℂ)=1 := by
  unfold finRealify
  rw [realify_one]
  ext i j
  simp [Matrix.one_apply]
lemma finRealify_add (A B : Matrix (Fin d) (Fin d) ℂ) :
    finRealify (A+B)=finRealify A+finRealify B := by
  simp only [finRealify,realify_add,Matrix.submatrix_add,Pi.add_apply]
lemma finRealify_smul (r : ℝ) (A : Matrix (Fin d) (Fin d) ℂ) :
    finRealify (r • A)=r • finRealify A := by
  simp only [finRealify,realify_smul,Matrix.submatrix_smul,Pi.smul_apply]
lemma finRealify_neg (A : Matrix (Fin d) (Fin d) ℂ) : finRealify (-A)= -finRealify A := by
  have h : realify (-A) = -realify A := by
    ext (i|i) (j|j) <;> simp [realify,Matrix.fromBlocks]
  simp only [finRealify,h,Matrix.submatrix_neg]
  rfl
lemma finRealify_sub (A B : Matrix (Fin d) (Fin d) ℂ) :
    finRealify (A-B)=finRealify A-finRealify B := by
  simp only [sub_eq_add_neg,finRealify_add,finRealify_neg]
lemma finRealify_mul (A B : Matrix (Fin d) (Fin d) ℂ) :
    finRealify (A*B)=finRealify A*finRealify B := by
  rw [finRealify,realify_mul]
  exact (Matrix.submatrix_mul_equiv _ _ _ finSumFinEquiv.symm _).symm
lemma finRealify_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix (Fin d) (Fin d) ℂ) :
    finRealify (∑ i ∈ s,A i)=∑ i ∈ s,finRealify (A i) := by
  ext i j
  simp only [finRealify,realify_sum,Matrix.submatrix_apply,Matrix.sum_apply]

end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_Lookup
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalFace
variable {N n : ℕ}

lemma activeIndices_mem (x : Fin N → ℚ) (i : Fin N) :
    i∈activeIndices x ↔ |x i|<1 := by simp [activeIndices]

end CurrentKS.RationalFace

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_Select
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Descent
variable {α : Type*}

lemma run_invariant (step : α → Option α) (P : α → Prop)
    (hp : ∀ x y,P x → step x=some y → P y) (k : ℕ) (x : α) (hx : P x) :
    P (run step k x) := by
  induction k generalizing x with
  | zero => exact hx
  | succ k ih =>
    simp only [run]
    split
    · exact hx
    · rename_i y hy
      exact ih y (hp x y hx hy)

theorem run_terminates (step : α → Option α) (P : α → Prop) (f : α → ℝ) {r : ℝ}
    (hr : 0 < r) (hf : ∀ x,P x → 0 ≤ f x)
    (hp : ∀ x y,P x → step x=some y → P y)
    (hd : ∀ x y,P x → step x=some y → f y ≤ f x-r)
    (k : ℕ) (x : α) (hx : P x) (hk : f x < k*r) : step (run step k x)=none := by
  induction k generalizing x with
  | zero => simp only [Nat.cast_zero,zero_mul] at hk; exact (not_lt_of_ge (hf x hx) hk).elim
  | succ k ih =>
    rw [run]
    cases he : step x with
    | none => exact he
    | some y =>
      apply ih y (hp x y hx he)
      have hdecrease := (div_le_div_iff_of_pos_right hr).2 (hd x y hx he)
      have hbound := (div_lt_iff₀ hr).2 hk
      apply (div_lt_iff₀ hr).1
      rw [sub_div, div_self (ne_of_gt hr)] at hdecrease
      push_cast at hbound
      linarith

end CurrentKS.Descent

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_MinList
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Descent

lemma minList_pos (l : List ℚ) (h : ∀ a∈l,0<a) : 0 < minList l := by
  induction l with
  | nil => norm_num [minList]
  | cons a as ih =>
    exact lt_min (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

lemma fuel_spec {r : ℚ} (hr : 0 < r) : (100:ℝ)<(fuel r:ℝ)*(r:ℝ) := by
  have hc : (100:ℚ)/r < (fuel r:ℚ) := by
    have hh := Nat.le_ceil (100/r)
    dsimp [fuel]
    push_cast
    linarith
  have hh : (100:ℚ)<(fuel r:ℚ)*r := (div_lt_iff₀ hr).mp hc
  exact_mod_cast hh

lemma run_value_le {α : Type*} (step : α → Option α) (P : α → Prop) (f : α → ℝ)
    (hp : ∀ x y,P x → step x=some y → P y)
    (hd : ∀ x y,P x → step x=some y → f y≤f x)
    (k : ℕ) (x : α) (hx : P x) : f (run step k x)≤f x := by
  induction k generalizing x with
  | zero => exact le_refl _
  | succ k ih =>
    rw [run]
    cases he : step x with
    | none => exact le_refl _
    | some y => exact (ih y (hp x y hx he)).trans (hd x y hx he)

end CurrentKS.Descent

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_NearestEndpoint
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalFace
variable {N : ℕ}

lemma nearestEndpoint_abs (r : ℚ) : |nearestEndpoint r|=1 := by
  unfold nearestEndpoint
  split <;> norm_num

lemma nearestEndpoint_dist {r : ℚ} (hr : |r|≤1) : |nearestEndpoint r-r|=1-|r| := by
  unfold nearestEndpoint
  split
  · rename_i h
    rw [abs_of_nonneg h,abs_of_nonneg (by linarith [(abs_le.mp hr).2])]
  · rename_i h
    have hn : r≤0 := (lt_of_not_ge h).le
    rw [abs_of_nonpos hn,abs_of_nonpos (by linarith [(abs_le.mp hr).1])]
    ring

lemma freezeOne_cube (σ : ℚ) (x : Fin N → ℚ) (hx : ∀ i,|x i|≤1) (i : Fin N) :
    ∀ j,|freezeOne σ x i j|≤1 := by
  unfold freezeOne
  split
  · intro j
    by_cases hj : j=i
    · subst j;simpa using (nearestEndpoint_abs (x i)).le
    · simpa only [Function.update_of_ne hj] using hx j
  · exact hx

lemma freezeOne_other (σ : ℚ) (x : Fin N → ℚ) (i j : Fin N) (hji : j≠i) :
    freezeOne σ x i j=x j := by
  unfold freezeOne
  split <;> simp [Function.update_of_ne hji]

lemma freezeOne_assigned (σ : ℚ) (x : Fin N → ℚ) (i : Fin N) :
    |freezeOne σ x i i|=1 ∨ σ<1-|freezeOne σ x i i| := by
  unfold freezeOne
  split
  · exact Or.inl (by simpa using nearestEndpoint_abs (x i))
  · exact Or.inr (lt_of_not_ge ‹¬1-|x i|≤σ›)

lemma freezeOne_preserves_assigned (σ : ℚ) (x : Fin N → ℚ) (i j : Fin N)
    (h : |x j|=1 ∨ σ<1-|x j|) :
    |freezeOne σ x i j|=1 ∨ σ<1-|freezeOne σ x i j| := by
  by_cases hji : j=i
  · subst j;exact freezeOne_assigned σ x i
  · simpa only [freezeOne_other σ x i j hji] using h

lemma freezeList_cube (σ : ℚ) (x : Fin N → ℚ) (hx : ∀ i,|x i|≤1) (l : List (Fin N)) :
    ∀ j,|freezeList σ x l j|≤1 := by
  induction l generalizing x with
  | nil => exact hx
  | cons i is ih => exact ih _ (freezeOne_cube σ x hx i)

lemma freezeList_preserves_assigned (σ : ℚ) (x : Fin N → ℚ) (l : List (Fin N)) (j : Fin N)
    (h : |x j|=1 ∨ σ<1-|x j|) :
    |freezeList σ x l j|=1 ∨ σ<1-|freezeList σ x l j| := by
  induction l generalizing x with
  | nil => exact h
  | cons i is ih => exact ih _ (freezeOne_preserves_assigned σ x i j h)

lemma freezeList_assigned (σ : ℚ) (x : Fin N → ℚ) (l : List (Fin N)) (j : Fin N) (hj : j∈l) :
    |freezeList σ x l j|=1 ∨ σ<1-|freezeList σ x l j| := by
  induction l generalizing x with
  | nil => simp at hj
  | cons i is ih =>
    rcases List.mem_cons.mp hj with hij|hj
    · subst j
      exact freezeList_preserves_assigned σ _ is i (freezeOne_assigned σ x i)
    · exact ih _ hj

lemma freezeAll_strip (σ : ℚ) (x : Fin N → ℚ) (j : Fin N)
    (hj : |freezeAll σ x j|<1) : |freezeAll σ x j|<1-σ := by
  have hh := freezeList_assigned σ x (List.finRange N) j (List.mem_finRange j)
  change |freezeAll σ x j|=1 ∨ σ<1-|freezeAll σ x j| at hh
  rcases hh with h|h <;> linarith

end CurrentKS.RationalFace

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Point
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma feasible_iff (S : H d) (η : H d →L[ℝ] H d) (z : Point d) :
    z ∈ feasible S η ↔ z.2.1 ∈ pd d ∧ z.2.2 ∈ pd d ∧
      invH z.2.1 + S + η z.2.2 ≤ z.1 • (Hermitian.one : H d) ∧
      invH z.2.2 - S + η z.2.1 ≤ z.1 • (Hermitian.one : H d) := by
  simp only [feasible, domain, residual, mem_ofPred_eq, sub_nonpos]
  tauto

lemma continuous_objective (ε : ℝ) : Continuous (objective (d := d) ε) := by
  exact continuous_fst.add (continuous_const.mul
    (continuous_realTrace.comp ((continuous_fst.comp continuous_snd).add
      (continuous_snd.comp continuous_snd))))

lemma trace_bounds_of_feasible [NeZero d] (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d, η A ∈ psdCone d)
    {z : Point d} (hz : z ∈ feasible S η) :
    0 ≤ z.1 ∧ 0 ≤ _root_.OAI.CurrentKS.Hermitian.realTrace z.2.1 ∧ 0 ≤ _root_.OAI.CurrentKS.Hermitian.realTrace z.2.2 := by
  obtain ⟨hX, hY, h₁, h₂⟩ := (feasible_iff S η z).mp hz
  have htr₁ := realTrace_mono h₁
  have htr₂ := realTrace_mono h₂
  have hiX := realTrace_nonneg (A := invH z.2.1) hX.inv.posSemidef
  have hiY := realTrace_nonneg (A := invH z.2.2) hY.inv.posSemidef
  have heX := realTrace_nonneg (hη _ hX.posSemidef)
  have heY := realTrace_nonneg (hη _ hY.posSemidef)
  simp only [realTrace_add, realTrace_sub, realTrace_smul, realTrace_one] at htr₁ htr₂
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  refine ⟨?_, realTrace_nonneg hX.posSemidef, realTrace_nonneg hY.posSemidef⟩
  nlinarith

lemma objective_bounds [NeZero d] (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d, η A ∈ psdCone d)
    {ε K : ℝ} (hε : 0 < ε) {z : Point d} (hz : z ∈ feasible S η)
    (hf : objective ε z ≤ K) :
    0 ≤ z.1 ∧ z.1 ≤ K ∧ _root_.OAI.CurrentKS.Hermitian.realTrace z.2.1 ≤ K / ε ∧ _root_.OAI.CurrentKS.Hermitian.realTrace z.2.2 ≤ K / ε := by
  obtain ⟨ht, hX, hY⟩ := trace_bounds_of_feasible S η hη hz
  simp only [objective, realTrace_add] at hf
  refine ⟨ht, ?_, (le_div_iff₀ hε).mpr ?_, (le_div_iff₀ hε).mpr ?_⟩ <;>
    nlinarith [mul_nonneg hε.le hX, mul_nonneg hε.le hY]

lemma inverse_bounds (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d, η A ∈ psdCone d)
    {K : ℝ} (hS₁ : -K • (Hermitian.one : H d) ≤ S) (hS₂ : S ≤ K • (Hermitian.one : H d))
    {z : Point d} (hz : z ∈ feasible S η) (ht : z.1 ≤ K) :
    invH z.2.1 ≤ (2*K) • (Hermitian.one : H d) ∧ invH z.2.2 ≤ (2*K) • (Hermitian.one : H d) := by
  obtain ⟨hX, hY, h₁, h₂⟩ := (feasible_iff S η z).mp hz
  have heX : 0 ≤ η z.2.1 := psd_nonneg (hη _ hX.posSemidef)
  have heY : 0 ≤ η z.2.2 := psd_nonneg (hη _ hY.posSemidef)
  have htk : z.1 • (Hermitian.one : H d) ≤ K • (Hermitian.one : H d) := scalar_one_mono ht
  constructor
  · have hh : invH z.2.1 + S ≤ K • (Hermitian.one : H d) :=
      (le_add_of_nonneg_right heY).trans (h₁.trans htk)
    have hx := add_le_add hh (neg_le_neg hS₁)
    convert hx using 1 <;> first | rfl | module
  · have hh : invH z.2.2 - S ≤ K • (Hermitian.one : H d) :=
      (le_add_of_nonneg_right heX).trans (h₂.trans htk)
    have hx := add_le_add hh hS₂
    convert hx using 1 <;> first | rfl | module

lemma sublevel_box [NeZero d] (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d, η A ∈ psdCone d)
    {ε K : ℝ} (hε : 0 < ε) (hK : 0 < K)
    (hS₁ : -K • (Hermitian.one : H d) ≤ S) (hS₂ : S ≤ K • (Hermitian.one : H d))
    {z : Point d} (hz : z ∈ feasible S η) (hf : objective ε z ≤ K) :
    z.1 ∈ Icc 0 K ∧
    ((2*K)⁻¹ • (Hermitian.one : H d) ≤ z.2.1 ∧ z.2.1 ≤ (K/ε) • (Hermitian.one : H d)) ∧
    ((2*K)⁻¹ • (Hermitian.one : H d) ≤ z.2.2 ∧ z.2.2 ≤ (K/ε) • (Hermitian.one : H d)) := by
  obtain ⟨ht, htK, htrX, htrY⟩ := objective_bounds S η hη hε hz hf
  obtain ⟨hXi, hYi⟩ := inverse_bounds S η hη hS₁ hS₂ hz htK
  obtain ⟨hX,hY,-,-⟩ := (feasible_iff S η z).mp hz
  have hmul : ∀ r s : ℝ, r ≤ s → r • (Hermitian.one : H d) ≤ s • (Hermitian.one : H d) :=
    fun _ _ h => scalar_one_mono h
  exact ⟨⟨ht,htK⟩,
    ⟨inverse_bound_below (by positivity) hX hXi,
      (trace_bound_above hX.posSemidef).trans (hmul _ _ htrX)⟩,
    ⟨inverse_bound_below (by positivity) hY hYi,
      (trace_bound_above hY.posSemidef).trans (hmul _ _ htrY)⟩⟩

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_PairCone
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma isClosed_pairCone : IsClosed (pairCone d : Set (H d × H d)) :=
  (isClosed_psdCone (d := d)).prod (isClosed_psdCone (d := d))

lemma feasible_iff_cone (S : H d) (η : H d →L[ℝ] H d) (z : Point d) :
    z ∈ feasible S η ↔ z ∈ domain d ∧ -residual S η z ∈ pairCone d := by
  simp only [feasible, mem_ofPred_eq, mem_pairCone, Prod.fst_neg, Prod.snd_neg]
  simp only [mem_psd_iff_nonneg, neg_nonneg]

lemma continuousOn_residual (S : H d) (η : H d →L[ℝ] H d) :
    ContinuousOn (residual S η) (domain d) := by
  intro z hz
  have hiX : ContinuousAt (fun z : Point d => invH z.2.1) z :=
    (continuousAt_invH hz.1).comp (f := fun w : Point d => w.2.1) (x := z) (by fun_prop)
  have hiY : ContinuousAt (fun z : Point d => invH z.2.2) z :=
    (continuousAt_invH hz.2).comp (f := fun w : Point d => w.2.2) (x := z) (by fun_prop)
  have heX : ContinuousAt (fun z : Point d => η z.2.1) z :=
    η.continuous.continuousAt.comp (f := fun w : Point d => w.2.1) (x := z) (by fun_prop)
  have heY : ContinuousAt (fun z : Point d => η z.2.2) z :=
    η.continuous.continuousAt.comp (f := fun w : Point d => w.2.2) (x := z) (by fun_prop)
  exact (((hiX.add continuousAt_const).add heY).sub
    (continuousAt_fst.smul continuousAt_const)).prodMk
      (((hiY.sub continuousAt_const).add heX).sub
        (continuousAt_fst.smul continuousAt_const)) |>.continuousWithinAt

theorem exists_minimizer [NeZero d] (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d, η A ∈ psdCone d)
    {ε K : ℝ} (hε : 0 < ε) (hK : 0 < K)
    (hS₁ : -K • (Hermitian.one : H d) ≤ S) (hS₂ : S ≤ K • (Hermitian.one : H d))
    (z₀ : Point d) (hz₀ : z₀ ∈ feasible S η) (hf₀ : objective ε z₀ ≤ K) :
    ∃ z ∈ feasible S η, objective ε z ≤ K ∧
      ∀ w ∈ feasible S η, objective ε z ≤ objective ε w := by
  let B : Set (Point d) := Icc 0 K ×ˢ
    ({A : H d | (2*K)⁻¹ • (Hermitian.one : H d) ≤ A ∧ A ≤ (K/ε) • (Hermitian.one : H d)} ×ˢ
      {A : H d | (2*K)⁻¹ • (Hermitian.one : H d) ≤ A ∧ A ≤ (K/ε) • (Hermitian.one : H d)})
  have hBc : IsCompact B := isCompact_Icc.prod
    ((isCompact_orderBox _ _).prod (isCompact_orderBox _ _))
  have hBD : B ⊆ domain d := by
    intro z hz
    exact ⟨pd_of_lower (by positivity) hz.2.1.1, pd_of_lower (by positivity) hz.2.2.1⟩
  let F : Point d → (H d × H d) × ℝ := fun z => (-residual S η z, objective ε z)
  have hFc : ContinuousOn F B := ((continuousOn_residual S η).mono hBD).neg.prodMk
    (continuous_objective ε).continuousOn
  let C : Set (Point d) := B ∩ F ⁻¹' ((pairCone d : Set (H d × H d)) ×ˢ Iic K)
  have hCc : IsClosed C := hFc.preimage_isClosed_of_isClosed hBc.isClosed
    (isClosed_pairCone.prod isClosed_Iic)
  have hCcompact : IsCompact C := hBc.of_isClosed_subset hCc inter_subset_left
  have hCm (z : Point d) : z ∈ C ↔ z ∈ B ∧ z ∈ feasible S η ∧ objective ε z ≤ K := by
    simp only [C, mem_inter_iff, mem_preimage, mem_prod, mem_Iic, F]
    constructor
    · rintro ⟨hz, hc, hf⟩
      exact ⟨hz, (feasible_iff_cone S η z).mpr ⟨hBD hz, hc⟩, hf⟩
    · rintro ⟨hz, hc, hf⟩
      exact ⟨hz, ((feasible_iff_cone S η z).mp hc).2, hf⟩
  have hnonempty : C.Nonempty := by
    refine ⟨z₀, (hCm z₀).mpr ⟨?_, hz₀, hf₀⟩⟩
    exact sublevel_box S η hη hε hK hS₁ hS₂ hz₀ hf₀
  obtain ⟨z, hz, hmin⟩ := hCcompact.exists_isMinOn hnonempty (continuous_objective ε).continuousOn
  have hzm := (hCm z).mp hz
  refine ⟨z, hzm.2.1, hzm.2.2, fun w hw => ?_⟩
  by_cases hfw : objective ε w ≤ K
  · apply hmin
    exact (hCm w).mpr ⟨sublevel_box S η hη hε hK hS₁ hS₂ hw hfw, hw, hfw⟩
  · exact hzm.2.2.trans (le_of_lt (lt_of_not_ge hfw))

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Coordinates
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.State.line_zero _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.State
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

attribute [local instance] OAI.CurrentKS.State.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p1
private local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_r975388_1 : NormedSpace ℝ (H d) := inferInstance
attribute [local instance] OAI.CurrentKS.State.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p1
lemma eta_apply (c : ℝ) (A : Fin N → H d) (x : Coordinates N) (Z : H d) :
    eta c A x Z = ∑ i, (c * psi (x i)) • sandwich (A i) Z := by
  simp [eta]

lemma psi_bounds {x : ℝ} (hx : |x| ≤ 1) : 0 ≤ psi x ∧ psi x ≤ 1 := by
  have hr : 0 ≤ 1-x^2 := by have hh := abs_le.mp hx; nlinarith
  exact ⟨Real.rpow_nonneg hr _, Real.rpow_le_one hr (by nlinarith [sq_nonneg x]) (by norm_num)⟩

lemma eta_positive {c : ℝ} (hc : 0 ≤ c) (A : Fin N → H d) {x : Coordinates N} (hx : Cube x) :
    ∀ Z ∈ psdCone d, eta c A x Z ∈ psdCone d := by
  intro Z hZ
  rw [eta_apply]
  exact psd_sum _ _ fun i _ => psd_smul (sandwich_psd _ _ hZ) (mul_nonneg hc (psi_bounds (hx i)).1)

lemma sum_le_one (A : Fin N → H d) (hA : ∀ i, A i ∈ psdCone d)
    (htr : ∑ i, _root_.OAI.CurrentKS.Hermitian.realTrace (A i) = 1) : (∑ i, A i) ≤ (Hermitian.one : H d) := by
  have hp := trace_bound_above (psd_sum Finset.univ A fun i _ => hA i)
  simpa only [realTrace_sum,htr,one_smul] using hp

lemma S_bounds (A : Fin N → H d) (hA : ∀ i, A i ∈ psdCone d)
    (htr : ∑ i, _root_.OAI.CurrentKS.Hermitian.realTrace (A i) = 1) {x : Coordinates N} (hx : Cube x) :
    -(Hermitian.one : H d) ≤ S A x ∧ S A x ≤ (Hermitian.one : H d) := by
  have hsum := sum_le_one A hA htr
  have hupper : S A x ≤ ∑ i, A i := by
    apply Finset.sum_le_sum
    intro i _
    simpa only [one_smul] using scalar_mono_psd (hA i) (abs_le.mp (hx i)).2
  have hlower : -(∑ i, A i) ≤ S A x := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hh := scalar_mono_psd (hA i) (abs_le.mp (hx i)).1
    have he : (-1 : ℝ) • A i = -A i := neg_one_smul ℝ (A i)
    rw [he] at hh
    exact hh
  exact ⟨(neg_le_neg hsum).trans hlower,hupper.trans hsum⟩

lemma eta_one_bound {c ν : ℝ} (hc : 0 ≤ c) (A : Fin N → H d)
    (hν : (∑ i, sandwich (A i) (Hermitian.one : H d)) ≤ ν • (Hermitian.one : H d))
    {x : Coordinates N} (hx : Cube x) : eta c A x (Hermitian.one : H d) ≤ (c*ν) • (Hermitian.one : H d) := by
  rw [eta_apply,SemigroupAction.mul_smul]
  apply le_trans _ (smul_order hν hc)
  rw [Finset.smul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact scalar_mono_psd (sandwich_psd _ _ one_mem_psdCone)
    (mul_le_of_le_one_right hc (psi_bounds (hx i)).2)

end CurrentKS.State

namespace CurrentKS.Variational
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma scalar_feasible (S : H d) (η : H d →L[ℝ] H d) {s b a : ℝ}
    (hs₁ : -s • (Hermitian.one : H d) ≤ S) (hs₂ : S ≤ s • (Hermitian.one : H d))
    (hb : η (Hermitian.one : H d) ≤ b • (Hermitian.one : H d)) (ha : 0 < a) :
    (s+a⁻¹+b*a, a • (Hermitian.one : H d), a • (Hermitian.one : H d)) ∈ feasible S η := by
  have hpd := pd_smul (show (Hermitian.one : H d) ∈ pd d from Matrix.PosDef.one) ha
  apply (feasible_iff _ _ _).mpr
  refine ⟨hpd,hpd,?_,?_⟩
  · change invH (a • (Hermitian.one : H d)) + S + η (a • (Hermitian.one : H d)) ≤
      (s+a⁻¹+b*a) • (Hermitian.one : H d)
    rw [invH_scalar,map_smul]
    calc
      _ ≤ a⁻¹ • (Hermitian.one : H d) + s • (Hermitian.one : H d) + a • (b • (Hermitian.one : H d)) :=
        show a⁻¹ • (Hermitian.one : H d) + S + a • η (Hermitian.one : H d) ≤ _ from
          add_le_add (add_le_add (le_refl (a⁻¹ • (Hermitian.one : H d))) hs₂) (smul_order hb ha.le)
      _ = (s+a⁻¹+b*a) • (Hermitian.one : H d) := by
        rw [smul_smul,← add_smul,← add_smul]
        congr 1
        ring
  · change invH (a • (Hermitian.one : H d)) - S + η (a • (Hermitian.one : H d)) ≤
      (s+a⁻¹+b*a) • (Hermitian.one : H d)
    rw [invH_scalar,map_smul]
    have hns : -S ≤ s • (Hermitian.one : H d) := by
      have hh := neg_le_neg hs₁
      rw [neg_smul s (Hermitian.one : H d), neg_neg] at hh
      exact hh
    change a⁻¹ • (Hermitian.one : H d) + -S + a • η (Hermitian.one : H d) ≤ _
    calc
      _ ≤ a⁻¹ • (Hermitian.one : H d) + s • (Hermitian.one : H d) + a • (b • (Hermitian.one : H d)) :=
        add_le_add (add_le_add (le_refl (a⁻¹ • (Hermitian.one : H d))) hns) (smul_order hb ha.le)
      _ = (s+a⁻¹+b*a) • (Hermitian.one : H d) := by
        rw [smul_smul,← add_smul,← add_smul]
        congr 1
        ring

lemma scalar_objective (ε s b a : ℝ) :
    objective ε (s+a⁻¹+b*a, a • (Hermitian.one : H d), a • (Hermitian.one : H d)) =
      s+a⁻¹+(b+2*d*ε)*a := by
  simp only [objective,realTrace_add,realTrace_smul,realTrace_one]
  ring

end CurrentKS.Variational

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_NormalizedMinimizer
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Variational
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

theorem normalized_minimizer [NeZero d] (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d,η A ∈ psdCone d) {ε : ℝ} (hε : 0 < ε)
    (hεd : ε*d ≤ 1) (hlo : -(Hermitian.one : H d) ≤ S)
    (hhi : S ≤ (Hermitian.one : H d))
    (hηI : η (Hermitian.one : H d) ≤ (384:ℝ) • (Hermitian.one : H d)) :
    ∃ z ∈ feasible S η,objective ε z ≤ 100 ∧
      ∀ w ∈ feasible S η,objective ε z ≤ objective ε w := by
  have hlo' : -(100:ℝ) • (Hermitian.one : H d) ≤ S := by
    apply le_trans _ hlo
    have hc := scalar_mono_psd (d:=d) one_mem_psdCone (by norm_num : (-100:ℝ) ≤ -1)
    rw [neg_smul (1:ℝ) (Hermitian.one : H d),one_smul] at hc
    exact hc
  have hhi' : S ≤ (100:ℝ) • (Hermitian.one : H d) := by
    apply hhi.trans
    simpa only [one_smul] using scalar_mono_psd one_mem_psdCone (by norm_num : (1:ℝ) ≤ 100)
  let z₀ : Point d := (1+(1/20:ℝ)⁻¹+384*(1/20),(1/20:ℝ) • (Hermitian.one : H d),(1/20:ℝ) • (Hermitian.one : H d))
  have hz₀ : z₀ ∈ feasible S η :=
    scalar_feasible S η (s:=1) (b:=384) (a:=1/20)
      (by rw [neg_smul (1:ℝ) (Hermitian.one : H d),one_smul]; exact hlo)
      (by simpa only [one_smul] using hhi) hηI (by norm_num)
  have hf : objective ε z₀ ≤ 100 := by
    dsimp [z₀]
    rw [scalar_objective]
    norm_num
    nlinarith
  exact exists_minimizer S η hη hε (by norm_num) hlo' hhi' z₀ hz₀ hf
end CurrentKS.Variational

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Value
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma value_eq_of_min (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d)
    (z : Point d) (hz : z ∈ feasible S η)
    (hmin : ∀ w ∈ feasible S η, objective ε z ≤ objective ε w) :
    value ε S η = objective ε z := by
  apply IsLeast.csInf_eq
  refine ⟨⟨z,hz,rfl⟩,?_⟩
  rintro b ⟨w,hw,rfl⟩
  exact hmin w hw

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_CoarseBudget
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Calculus Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d N : ℕ}

lemma coarseBudget_bounds {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) :
    1 ≤ coarseBudget d N ε σ ∧ (d:ℝ)+1 ≤ coarseBudget d N ε σ ∧
    |ε| ≤ coarseBudget d N ε σ ∧
    200+(200/ε)*((d:ℝ)+1) ≤ coarseBudget d N ε σ ∧
    200*((d:ℝ)+1) ≤ coarseBudget d N ε σ ∧
    ((d:ℝ)+1)+N ≤ coarseBudget d N ε σ ∧
    384*N*(1+800/σ^3) ≤ coarseBudget d N ε σ := by
  have hd : 0 ≤ (d:ℝ)+1 := by positivity
  have hn : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
  have hp : 0 ≤ (200/ε)*((d:ℝ)+1) := by positivity
  have hr : 0 ≤ 384*(N:ℝ)*(1+800/σ^3) := by positivity
  have he := abs_nonneg ε
  dsimp [coarseBudget]
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor <;> linarith

end
end CurrentKS.State

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_ValueFeasible
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d : ℕ}

attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p8
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealSubtypeMatMemSubmoduleH_p8
attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p8
attribute [local instance] OAI.CurrentKS.Variational.valueFeasibleOperatorNormedAddCommGroup
attribute [local instance] OAI.CurrentKS.Variational.valueFeasibleOperatorNormedSpace
attribute [local instance] OAI.CurrentKS.Variational.valueFeasiblePairNormedSpace
lemma value_le_feasible [NeZero d] (ε : ℝ) (hε : 0 ≤ ε) (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d, η A ∈ psdCone d) (z : Point d) (hz : z ∈ feasible S η) :
    value ε S η ≤ objective ε z := by
  have hb : BddBelow (objective ε '' feasible S η) := by
    refine ⟨0,?_⟩
    rintro r ⟨w,hw,rfl⟩
    obtain ⟨ht,hX,hY⟩ := trace_bounds_of_feasible S η hη hw
    simp only [objective,realTrace_add]
    exact add_nonneg ht (mul_nonneg hε (add_nonneg hX hY))
  exact csInf_le hb ⟨z,hz,rfl⟩

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_SquareInterval
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalRoot

lemma squareInterval_spec (q : ℚ) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hq : (q:ℝ)=r^2) (k : ℕ) :
    0 ≤ (squareInterval q k).1 ∧ (squareInterval q k).2 ≤ 1 ∧
    ((squareInterval q k).1:ℝ) ≤ r ∧ r ≤ ((squareInterval q k).2:ℝ) ∧
    (squareInterval q k).2-(squareInterval q k).1=(1/2:ℚ)^k := by
  induction k with
  | zero => simpa [squareInterval] using And.intro hr hr1
  | succ k ih =>
    have horder : (squareInterval q k).1 ≤ (squareInterval q k).2 := by
      exact_mod_cast ih.2.2.1.trans ih.2.2.2.1
    let m : ℚ := ((squareInterval q k).1+(squareInterval q k).2)/2
    have hml : (squareInterval q k).1 ≤ m := by dsimp [m] <;> linarith
    have hmu : m ≤ (squareInterval q k).2 := by dsimp [m] <;> linarith
    have hm : 0 ≤ m := ih.1.trans hml
    have hmr : (0:ℝ) ≤ m := by exact_mod_cast hm
    have he : squareInterval q (k+1) = if m^2 ≤ q then (m,(squareInterval q k).2) else ((squareInterval q k).1,m) := rfl
    rw [he]
    split
    · rename_i h
      have hc : (m:ℝ)^2 ≤ r^2 := by rw [← hq]; exact_mod_cast h
      have hle := (pow_le_pow_iff_left₀ hmr hr (by decide : 2≠0)).mp hc
      refine ⟨hm,ih.2.1,hle,ih.2.2.2.1,?_⟩
      change (squareInterval q k).2-m=(1/2:ℚ)^(k+1)
      rw [pow_succ,← ih.2.2.2.2]
      dsimp [m]
      ring
    · rename_i h
      have hc : r^2 ≤ (m:ℝ)^2 := by rw [← hq]; exact_mod_cast (le_of_lt (lt_of_not_ge h))
      have hle := (pow_le_pow_iff_left₀ hr hmr (by decide : 2≠0)).mp hc
      refine ⟨ih.1,hmu.trans ih.2.1,ih.2.2.1,hle,?_⟩
      change m-(squareInterval q k).1=(1/2:ℚ)^(k+1)
      rw [pow_succ,← ih.2.2.2.2]
      dsimp [m]
      ring

lemma squareInterval_upper_error (q : ℚ) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hq : (q:ℝ)=r^2) (k : ℕ) :
    |((squareInterval q k).2:ℝ)-r| ≤ (1/2:ℝ)^k := by
  obtain ⟨_,_,hl,hu,hw⟩ := squareInterval_spec q r hr hr1 hq k
  have hwr : ((squareInterval q k).2:ℝ)-(squareInterval q k).1=(1/2:ℝ)^k := by
    have hc := congrArg (fun z : ℚ => (z : ℝ)) hw
    norm_num only [Rat.cast_sub,Rat.cast_pow,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at hc
    exact hc
  rw [abs_of_nonneg (sub_nonneg.mpr hu)]
  linarith

lemma inverse_pow_size_le {δ : ℚ} (hδ : 0 < δ) : (1/2:ℚ)^δ.den.size ≤ δ := by
  have hd : (0:ℚ) < δ.den := by exact_mod_cast δ.den_pos
  have hp : (0:ℚ) < 2^δ.den.size := by positivity
  have hnum : (1:ℚ) ≤ δ.num := by exact_mod_cast (Int.add_one_le_iff.mpr (Rat.num_pos.mpr hδ))
  have hden : (δ.den:ℚ) ≤ 2^δ.den.size := by exact_mod_cast (Nat.lt_size_self δ.den).le
  rw [_root_.one_div_pow,one_div]
  calc
    (2^δ.den.size:ℚ)⁻¹ ≤ (δ.den:ℚ)⁻¹ := inv_anti₀ hd hden
    _ ≤ (δ.num:ℚ)/(δ.den:ℚ) := by rw [inv_eq_one_div]; exact div_le_div_of_nonneg_right hnum hd.le
    _ = δ := Rat.num_div_den δ

theorem upperSqrt_spec (q δ : ℚ) (hδ : 0 < δ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    Real.sqrt (q:ℝ) ≤ (upperSqrt q δ:ℝ) ∧
    (upperSqrt q δ:ℝ) ≤ Real.sqrt (q:ℝ)+(δ:ℝ) := by
  have hr := Real.sqrt_nonneg (q:ℝ)
  have hr1 : Real.sqrt (q:ℝ) ≤ 1 := by
    exact (Real.sqrt_le_one).mpr (by exact_mod_cast hq1)
  have he : (q:ℝ) = Real.sqrt (q:ℝ)^2 := (Real.sq_sqrt (by exact_mod_cast hq)).symm
  have hs := squareInterval_spec q (Real.sqrt q) hr hr1 he δ.den.size
  have herror := squareInterval_upper_error q (Real.sqrt q) hr hr1 he δ.den.size
  have hh : (1/2:ℝ)^δ.den.size ≤ (δ:ℝ) := by
    have h := Rat.cast_le (K := ℝ).mpr (inverse_pow_size_le hδ)
    norm_num only [Rat.cast_pow,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at h
    exact h
  refine ⟨hs.2.2.2.1,?_⟩
  have hm := (abs_le.mp herror).2
  dsimp [upperSqrt]
  linarith

end CurrentKS.RationalRoot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_FacePotential
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.State
open CurrentKS.Scalar CurrentKS.Calculus
open scoped BigOperators ContDiff

variable {d N : ℕ}

open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Calculus Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff


lemma valueCurve_bounds_nonneg {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) :
    0 ≤ valueCurve2Bound d N ε σ ∧ 0 ≤ valueCurve3Bound d N ε σ := by
  have hB := (coarseBudget_bounds (d:=d) (N:=N) hε hσ).1
  dsimp [valueCurve2Bound,valueCurve3Bound]
  constructor <;> positivity

end CurrentKS.State

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Potential
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.State.line_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

lemma sum_update_composite {α β : Type*} [AddCommGroup β] (f : Fin N → α → β)
    (x : Fin N → α) (i : Fin N) (a : α) :
    (∑ j, f j (Function.update x i a j)) = (∑ j, f j (x j))+f i a-f i (x i) := by
  simp only [Function.apply_update]
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  have he := Finset.sum_erase_add Finset.univ (fun j => f j (x j)) (Finset.mem_univ i)
  rw [Finset.sdiff_singleton_eq_erase]
  rw [← he]
  abel

lemma S_update (A : Fin N → H d) (x : Coordinates N) (i : Fin N) (t : ℝ) :
    S A (Function.update x i t) = S A x+(t-x i) • A i := by
  rw [S,sum_update_composite (fun (j : Fin N) (r : ℝ) => r • A j) x i t]
  simp only [S]
  module

lemma eta_update (c : ℝ) (A : Fin N → H d) (x : Coordinates N) (i : Fin N) (t : ℝ) (Z : H d) :
    eta c A (Function.update x i t) Z = eta c A x Z+(c*(psi t-psi (x i))) • sandwich (A i) Z := by
  rw [eta_apply,sum_update_composite (fun (j : Fin N) (r : ℝ) => (c*psi r) • sandwich (A j) Z) x i t,eta_apply]
  module

lemma psi_endpoint {t : ℝ} (ht : |t| = 1) : psi t = 0 := by
  have hh : t^2 = 1 := by nlinarith [sq_abs t]
  simp [psi,hh]

lemma Cube_update {x : Coordinates N} (hx : Cube x) (i : Fin N) {t : ℝ} (ht : |t| ≤ 1) :
    Cube (Function.update x i t) := by
  intro j
  by_cases hj : j=i
  · subst j; simpa using ht
  · simpa [Function.update_of_ne hj] using hx j

end
end CurrentKS.State

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_MovementBudget
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Schedule

lemma movementBudget_one_le (n : ℕ) (ε : ℚ) : 1 ≤ movementBudget n ε := le_max_left _ _

lemma movementBudget_pos (n : ℕ) (ε : ℚ) : 0 < movementBudget n ε :=
  lt_of_lt_of_le (by norm_num) (movementBudget_one_le n ε)

lemma threshold_pos (n : ℕ) (ε : ℚ) {lam : ℚ} (hlam : 0 < lam) : 0 < threshold n ε lam := by
  unfold threshold
  have hp := movementBudget_pos n ε
  positivity

lemma stepSize_spec {a M σ : ℚ} (ha : 0 < a) (hM : 0 < M) (hσ : 0 < σ) :
    0 < stepSize a M σ ∧ stepSize a M σ ≤ σ/4 ∧ stepSize a M σ ≤ 1/4 ∧
      M*stepSize a M σ ≤ a/4 := by
  have hp : 0 < a/(4*M) := by positivity
  have hs : stepSize a M σ ≤ a/(4*M) := min_le_right _ _ |>.trans (min_le_left _ _)
  refine ⟨by unfold stepSize;positivity,min_le_left _ _,
    (min_le_right _ _).trans (min_le_right _ _),?_⟩
  have hh := (le_div_iff₀ (show (0:ℚ) < 4*M by positivity)).mp hs
  linarith

open CurrentKS.State

lemma coarseBudgetQ_cast (d n : ℕ) (ε σ : ℚ) :
    (coarseBudgetQ d n ε σ:ℝ)=coarseBudget d n (ε:ℝ) (σ:ℝ) := by
  simp only [coarseBudgetQ,coarseBudget,Rat.cast_add,Rat.cast_mul,Rat.cast_div,
    Rat.cast_pow,Rat.cast_natCast,Rat.cast_abs,Rat.cast_ofNat,Rat.cast_one]

lemma curveBudget_cast (d n : ℕ) (ε σ lam : ℚ) :
    (curveBudget d n ε σ lam:ℝ)=potentialCurveBound d n (ε:ℝ) (σ:ℝ) (lam:ℝ) := by
  simp only [curveBudget,potentialCurveBound,valueCurve2Q,valueCurve3Q,
    valueCurve2Bound,valueCurve3Bound,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,
    Rat.cast_natCast,Rat.cast_abs,Rat.cast_inv,Rat.cast_one,Rat.cast_ofNat,coarseBudgetQ_cast]

lemma curveBudget_one_le (d n : ℕ) {ε σ : ℚ} (hε : 0 < ε) (hσ : 0 < σ) (lam : ℚ) :
    1 ≤ curveBudget d n ε σ lam := by
  have hεr : (0:ℝ) < ε := by exact_mod_cast hε
  have hσr : (0:ℝ) < σ := by exact_mod_cast hσ
  have hh := valueCurve_bounds_nonneg (d:=d) (N:=n) hεr hσr
  have hl : (0:ℝ) ≤ |(lam:ℝ)| *(n:ℝ)*(1+800/(σ:ℝ)^3) := by positivity
  have hc : (1:ℝ) ≤ potentialCurveBound d n (ε:ℝ) (σ:ℝ) (lam:ℝ) := by
    unfold potentialCurveBound
    linarith
  rw [←curveBudget_cast] at hc
  exact_mod_cast hc

end CurrentKS.Schedule

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_FaceState
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalFace
noncomputable section
open CurrentKS.Hermitian CurrentKS.State CurrentKS.Variational CurrentKS.Scalar
open CurrentKS.RationalSDP CurrentKS.Schedule CurrentKS.Difference
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius ContDiff

variable {d N : ℕ}

lemma epsilon_spec [NeZero d] {ν : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) :
    0 < ν/(d:ℚ) ∧ ν/(d:ℚ) ≤ 1 ∧ ν/(d:ℚ)*(d:ℚ) ≤ 1 := by
  have hd : (0:ℚ) < d := by exact_mod_cast NeZero.pos d
  have hd1 : (1:ℚ) ≤ d := by exact_mod_cast NeZero.pos d
  refine ⟨div_pos hν hd,(div_le_one hd).mpr (hν1.trans hd1),?_⟩
  simpa only [div_mul_cancel₀ _ hd.ne'] using hν1

end
end CurrentKS.RationalFace

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_ShiftFeasibleMap
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.State.line_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Variational
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma shift_feasible_of_map_le (S T : H d) (η θ : H d →L[ℝ] H d)
    {r : ℝ} (hplus : T-S ≤ r • (Hermitian.one : H d))
    (hminus : S-T ≤ r • (Hermitian.one : H d))
    (hle : ∀ X ∈ psdCone d, θ X ≤ η X) (z : Point d) (hz : z ∈ feasible S η) :
    (z.1+r,z.2) ∈ feasible T θ := by
  rw [feasible_iff] at hz ⊢
  refine ⟨hz.1,hz.2.1,?_,?_⟩
  · have h := add_le_add hz.2.2.1 hplus
    have he : invH z.2.1+T+θ z.2.2 ≤ invH z.2.1+S+η z.2.2+(T-S) := by
      have hh := add_le_add_left (hle z.2.2 (show z.2.2 ∈ psdCone d from hz.2.1.posSemidef)) (invH z.2.1+T)
      convert hh using 1 <;> first | rfl | abel
    convert he.trans h using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | module
  · have h := add_le_add hz.2.2.2 hminus
    have he : invH z.2.2-T+θ z.2.1 ≤ invH z.2.2-S+η z.2.1+(S-T) := by
      have hh := add_le_add_left (hle z.2.1 (show z.2.1 ∈ psdCone d from hz.1.posSemidef)) (invH z.2.2-T)
      convert hh using 1 <;> first | rfl | abel
    convert he.trans h using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | module

end CurrentKS.Variational

namespace CurrentKS.State
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

lemma endpoint_eta_le {c : ℝ} (hc : 0 ≤ c) (A : Fin N → H d) (x : Coordinates N)
    (hx : Cube x) (i : Fin N) {t : ℝ} (ht : |t|=1) :
    ∀ X ∈ psdCone d,eta c A (Function.update x i t) X ≤ eta c A x X := by
  intro X hX
  rw [eta_update,psi_endpoint ht]
  have hs : (c*(0-psi (x i))) • sandwich (A i) X ≤ 0 := by
    simpa only [zero_smul] using scalar_mono_psd (sandwich_psd (A i) X hX)
      (show c*(0-psi (x i)) ≤ 0 by nlinarith [(psi_bounds (hx i)).1])
  simpa only [zero_add,add_comm] using add_le_add_left hs (eta c A x X)

lemma negative_le_operatorNorm (A : H d) : -A ≤ operatorNorm A • (Hermitian.one : H d) := by
  have h := le_operatorNorm_smul_one (-A)
  have he : operatorNorm (-A) = operatorNorm A := by
    rw [← neg_one_smul ℝ A,operatorNorm_smul]
    norm_num
  rwa [he] at h

lemma endpoint_value_shift [NeZero d] {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (A : Fin N → H d) (x : Coordinates N) (hx : Cube x) (i : Fin N) {t : ℝ}
    (ht : |t|=1) (z : Point d) (hz : z ∈ feasible (S A x) (eta c A x))
    (hmin : ∀ w ∈ feasible (S A x) (eta c A x),objective ε z ≤ objective ε w) :
    value ε (S A (Function.update x i t)) (eta c A (Function.update x i t)) ≤
      value ε (S A x) (eta c A x)+|t-x i| *operatorNorm (A i) := by
  let D := (t-x i) • A i
  have hd : S A (Function.update x i t)-S A x = D := by rw [S_update]; abel
  have hm : S A x-S A (Function.update x i t) = -D := by rw [S_update]; abel
  have hp : S A (Function.update x i t)-S A x ≤ operatorNorm D • (Hermitian.one : H d) := by
    rw [hd]; exact le_operatorNorm_smul_one D
  have hn : S A x-S A (Function.update x i t) ≤ operatorNorm D • (Hermitian.one : H d) := by
    rw [hm]; exact negative_le_operatorNorm D
  have hf := shift_feasible_of_map_le _ _ _ _ hp hn (endpoint_eta_le hc A x hx i ht) z hz
  have hv := value_le_feasible ε hε _ _ (eta_positive hc A (Cube_update hx i ht.le)) _ hf
  rw [value_eq_of_min ε _ _ z hz hmin]
  calc
    _ ≤ objective ε (z.1+operatorNorm D,z.2) := hv
    _ = objective ε z+|t-x i| *operatorNorm (A i) := by
      dsimp [objective,D]
      rw [operatorNorm_smul]
      ring

lemma endpoint_shift_potential [NeZero d] {c ε lam : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (A : Fin N → H d) (x : Coordinates N) (hx : Cube x) (i : Fin N) {t : ℝ}
    (ht : |t|=1) (z : Point d) (hz : z ∈ feasible (S A x) (eta c A x))
    (hmin : ∀ w ∈ feasible (S A x) (eta c A x),objective ε z ≤ objective ε w) :
    potential c ε lam A (Function.update x i t) ≤
      potential c ε lam A x+|t-x i| *operatorNorm (A i)-lam*psi (x i) := by
  have hv := endpoint_value_shift hc hε A x hx i ht z hz hmin
  rw [potential,potential,sum_update_composite (fun (_ : Fin N) (r : ℝ) => psi r) x i t,
    psi_endpoint ht,add_zero]
  nlinarith

lemma psi_sq_ge_distance {x : ℝ} (hx : |x| ≤ 1) : 1-|x| ≤ psi x^2 := by
  rcases lt_or_eq_of_le hx with hi|he
  · have hp := psi_pos hi
    have hc := psi_cube hi
    have h1 := psi_le_one hi
    have ha := abs_nonneg x
    have hr := sq_abs x
    have hprod := mul_nonneg (sq_nonneg (psi x)) (sub_nonneg.mpr h1)
    have hdist := mul_nonneg ha (sub_nonneg.mpr hx)
    nlinarith
  · rw [psi_endpoint he,he]; norm_num

lemma freeze_scalar {x lam ν : ℝ} (hx : |x| ≤ 1) (hlam : 0 ≤ lam) (hν : 0 < ν)
    (hclose : 1-|x| ≤ lam^2/ν) :
    (1-|x|)*Real.sqrt ν ≤ lam*psi x := by
  have hz : 0 ≤ 1-|x| := sub_nonneg.mpr hx
  have hv := Real.sq_sqrt hν.le
  have hr := Real.sq_sqrt hz
  have hab := (le_div_iff₀ hν).mp hclose
  have hp := (psi_bounds hx).1
  have hsp : Real.sqrt (1-|x|) ≤ psi x := by
    nlinarith [psi_sq_ge_distance hx,Real.sqrt_nonneg (1-|x|)]
  have hroot : Real.sqrt (1-|x|)*Real.sqrt ν ≤ lam := by
    have hs : (Real.sqrt (1-|x|)*Real.sqrt ν)^2 ≤ lam^2 := by
      rw [mul_pow,hr,hv];exact hab
    nlinarith [Real.sqrt_nonneg ν,Real.sqrt_nonneg (1-|x|)]
  have hh := mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg (1-|x|))
  have hh' : (1-|x|)*Real.sqrt ν ≤ lam*Real.sqrt (1-|x|) := by
    calc
      (1-|x|)*Real.sqrt ν = Real.sqrt (1-|x|)*(Real.sqrt (1-|x|)*Real.sqrt ν) := by rw [← mul_assoc,← sq,hr]
      _ ≤ Real.sqrt (1-|x|)*lam := hh
      _ = lam*Real.sqrt (1-|x|) := mul_comm _ _
  exact hh'.trans (mul_le_mul_of_nonneg_left hsp hlam)

theorem freeze_potential [NeZero d] {c ε lam ν : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (hlam : 0 ≤ lam) (hν : 0 < ν) (A : Fin N → H d) (x : Coordinates N)
    (hx : Cube x) (i : Fin N) {t : ℝ} (ht : |t|=1) (hne : |t-x i|=1-|x i|)
    (hAn : operatorNorm (A i) ≤ Real.sqrt ν) (hclose : 1-|x i| ≤ lam^2/ν)
    (z : Point d) (hz : z ∈ feasible (S A x) (eta c A x))
    (hmin : ∀ w ∈ feasible (S A x) (eta c A x),objective ε z ≤ objective ε w) :
    potential c ε lam A (Function.update x i t) ≤ potential c ε lam A x := by
  have he := endpoint_shift_potential hc hε A x hx i ht z hz hmin (lam:=lam)
  rw [hne] at he
  have hh := mul_le_mul_of_nonneg_left hAn (sub_nonneg.mpr (hx i))
  have hs := freeze_scalar (hx i) hlam hν hclose
  linarith

end CurrentKS.State

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_FreezePotential
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.State.line_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalFace
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.State CurrentKS.Variational
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

lemma freezeOne_potential [NeZero d] (A : Fin N → H d)
    (hA : ∀ i,A i∈psdCone d) (htr : ∑ i,Hermitian.realTrace (A i)=1)
    {ν lam ε : ℚ} (hν : 0<ν) (hν1 : ν≤1) (hlam : 0≤lam) (hε : 0<ε) (hεd : ε*d≤1)
    (hvar : (∑ i,sandwich (A i) (Hermitian.one : H d))≤(ν:ℝ) • (Hermitian.one : H d))
    (x : Fin N → ℚ) (hx : ∀ i,|x i|≤1) (i : Fin N) :
    potential 384 (ε:ℝ) (lam:ℝ) A (fun j => (freezeOne (lam^2/ν) x i j:ℝ))≤
      potential 384 (ε:ℝ) (lam:ℝ) A (fun j => (x j:ℝ)) := by
  unfold freezeOne
  split
  · rename_i hclose
    let xr : Coordinates N := fun j => (x j:ℝ)
    have hxr : Cube xr := fun j => by
      change |(x j:ℝ)| ≤ 1
      exact_mod_cast hx j
    have hord := S_bounds A hA htr hxr
    have ηbound := eta_one_bound (by norm_num : (0:ℝ)≤384) A hvar hxr
    have ηbound' : eta 384 A xr (Hermitian.one : H d)≤(384:ℝ) • (Hermitian.one : H d) := by
      apply ηbound.trans
      exact scalar_mono_psd one_mem_psdCone (by exact_mod_cast (show 384*ν≤(384:ℚ) by linarith))
    obtain ⟨z,hz,_,hmin⟩ := normalized_minimizer (ε:=(ε:ℝ)) (S A xr) (eta 384 A xr)
      (eta_positive (by norm_num : (0:ℝ)≤384) A hxr) (by exact_mod_cast hε)
      (by exact_mod_cast hεd) hord.1 hord.2 ηbound'
    have ht : |(nearestEndpoint (x i):ℝ)|=1 := by exact_mod_cast nearestEndpoint_abs (x i)
    have hdist : |(nearestEndpoint (x i):ℝ)-xr i|=1-|xr i| := by
      change |(nearestEndpoint (x i):ℝ)-(x i:ℝ)|=1-|(x i:ℝ)|
      exact_mod_cast nearestEndpoint_dist (hx i)
    have hh := freeze_potential (by norm_num : (0:ℝ)≤384) (ε:=(ε:ℝ)) (lam:=(lam:ℝ)) (ν:=(ν:ℝ))
      (by exact_mod_cast hε.le) (by exact_mod_cast hlam) (by exact_mod_cast hν) A xr hxr i ht hdist
      (atom_operatorNorm_le_sqrt A (by exact_mod_cast hν.le) hvar i)
      (by change 1-|(x i:ℝ)| ≤ (lam:ℝ)^2/(ν:ℝ); exact_mod_cast hclose) z hz hmin
    have heq : (fun j => (Function.update x i (nearestEndpoint (x i)) j : ℝ)) =
        Function.update xr i (nearestEndpoint (x i) : ℝ) := by
      ext j
      by_cases hji : j=i
      · subst j;simp
      · simp [Function.update_of_ne hji,xr]
    simpa only [heq] using hh
  · exact le_refl _

lemma freezeList_potential [NeZero d] (A : Fin N → H d)
    (hA : ∀ i,A i∈psdCone d) (htr : ∑ i,Hermitian.realTrace (A i)=1)
    {ν lam ε : ℚ} (hν : 0<ν) (hν1 : ν≤1) (hlam : 0≤lam) (hε : 0<ε) (hεd : ε*d≤1)
    (hvar : (∑ i,sandwich (A i) (Hermitian.one : H d))≤(ν:ℝ) • (Hermitian.one : H d))
    (x : Fin N → ℚ) (hx : ∀ i,|x i|≤1) (l : List (Fin N)) :
    potential 384 (ε:ℝ) (lam:ℝ) A (fun j => (freezeList (lam^2/ν) x l j:ℝ))≤
      potential 384 (ε:ℝ) (lam:ℝ) A (fun j => (x j:ℝ)) := by
  induction l generalizing x with
  | nil => exact le_refl _
  | cons i is ih =>
    exact (ih _ (freezeOne_cube _ _ hx i)).trans
      (freezeOne_potential A hA htr hν hν1 hlam hε hεd hvar x hx i)

end
end CurrentKS.RationalFace

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_Transition
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalFace
open CurrentKS.RationalSDP CurrentKS.Schedule CurrentKS.Difference CurrentKS.Descent

variable {d N : ℕ}

lemma freezeAll_stripCube (σ : ℚ) (x : Fin N → ℚ) (hx : ∀ i,|x i| ≤ 1) :
    StripCube σ (freezeAll σ x) :=
  ⟨freezeList_cube σ x hx _,fun i hi => (freezeAll_strip σ x i hi).le⟩

lemma uniformDrop_pos [NeZero d] {ν lam : ℚ} (hν : 0 < ν) (hlam : 0 < lam) :
    0 < uniformDrop d N ν lam := by
  apply minList_pos
  intro q hq
  obtain ⟨n,_,rfl⟩ := List.mem_map.mp hq
  have hd : (0:ℚ) < d := by exact_mod_cast NeZero.pos d
  have hε : 0 < ν/(d:ℚ) := div_pos hν hd
  have hσ : 0 < lam^2/ν := by positivity
  have ha := threshold_pos n (ν/(d:ℚ)) hlam
  have hM := curveBudget_one_le d n hε hσ lam
  have hs := stepSize_spec ha (lt_of_lt_of_le (by norm_num : (0:ℚ)<1) hM) hσ
  change 0 < threshold n (ν/(d:ℚ)) lam*(stepSize _ _ _)^2
  exact mul_pos ha (sq_pos_of_pos hs.1)

noncomputable section
open CurrentKS.Hermitian CurrentKS.State CurrentKS.Variational CurrentKS.Scalar
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

lemma fullPotential_freeze [NeZero d] (coords : Fin N → Fin d × Fin d → ℚ)
    (hA : ∀ i,rationalAtoms coords i∈psdCone d)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
    {ν lam : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hlam : 0 ≤ lam)
    (hvar : (∑ i,sandwich (rationalAtoms coords i) (Hermitian.one : H d)) ≤
      (ν:ℝ) • (Hermitian.one : H d))
    (x : Fin N → ℚ) (hx : ∀ i,|x i| ≤ 1) :
    fullPotential coords ν lam (freezeAll (lam^2/ν) x) ≤ fullPotential coords ν lam x := by
  have hep := epsilon_spec (d:=d) hν hν1
  exact freezeList_potential (rationalAtoms coords) hA htr hν hν1 hlam hep.1 hep.2.2 hvar x hx _

lemma terminal_vertex (coords : Fin N → Fin d × Fin d → ℚ) (ν lam : ℚ)
    (x : Fin N → ℚ) (hx : ∀ i,|x i| ≤ 1) (ht : transition coords ν lam x=none) :
    ∀ i,|x i|=1 := by
  have hn : (activeIndices x).length=0 := by
    by_contra hn
    simp only [transition,dite_eq_right hn] at ht
    contradiction
  have he : activeIndices x=[] := List.length_eq_zero_iff.mp hn
  intro i
  apply le_antisymm (hx i)
  by_contra hh
  have hh' : |x i|<1 := lt_of_not_ge hh
  have hm := (activeIndices_mem x i).mpr hh'
  exact List.not_mem_nil (he ▸ hm)

end
end CurrentKS.RationalFace

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_VarianceH
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.State.line_zero _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.State
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

lemma varianceH_psd (A : Fin N → H d) : varianceH A ∈ psdCone d :=
  psd_sum Finset.univ _ fun index _ => sandwich_psd (A index) _ one_mem_psdCone

lemma trace_each_le_one (A : Fin N → H d) (hA : ∀ i, A i ∈ psdCone d)
    (htr : ∑ i,Hermitian.realTrace (A i) = 1) (i : Fin N) : Hermitian.realTrace (A i) ≤ 1 := by
  rw [← htr]
  exact Finset.single_le_sum (fun j _ => realTrace_nonneg (hA j)) (Finset.mem_univ i)

lemma varianceH_le_one (A : Fin N → H d) (hA : ∀ i, A i ∈ psdCone d)
    (hrank : ∀ i, (A i : Mat d).rank ≤ 1) (htr : ∑ i,Hermitian.realTrace (A i) = 1) :
    varianceH A ≤ (Hermitian.one : H d) := by
  apply le_trans _ (sum_le_one A hA htr)
  apply Finset.sum_le_sum
  intro i _
  rw [sandwich_rank_one (A i) _ (hA i) (hrank i),inner_one']
  simpa only [one_smul] using scalar_mono_psd (hA i) (trace_each_le_one A hA htr i)

lemma varianceH_pos [NeZero d] (A : Fin N → H d) (_hA : ∀ i, A i ∈ psdCone d)
    (htr : ∑ i,Hermitian.realTrace (A i) = 1) : 0 < operatorNorm (varianceH A) := by
  apply lt_of_le_of_ne (operatorNorm_nonneg _)
  intro heq
  have hzero : varianceH A = 0 := (operatorNorm_eq_zero_iff _).mp heq.symm
  have hz (i : Fin N) : A i = 0 := by
    have hle : sandwich (A i) (Hermitian.one : H d) ≤ varianceH A :=
      Finset.single_le_sum (fun j _ => psd_nonneg (sandwich_psd (A j) _ one_mem_psdCone)) (Finset.mem_univ i)
    rw [hzero] at hle
    have hh : sandwich (A i) (Hermitian.one : H d) = 0 :=
      le_antisymm hle (psd_nonneg (sandwich_psd _ _ one_mem_psdCone))
    exact (sandwich_eq_zero_iff (A i) (Hermitian.one : H d) Matrix.PosDef.one).mp hh
  have ht : (∑ i,Hermitian.realTrace (A i)) = 0 := by simp only [hz,realTrace_zero,Finset.sum_const_zero]
  linarith

lemma feasible_norm_le_objective [NeZero d] (ε : ℝ) (hε : 0 ≤ ε) (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ Z ∈ psdCone d, η Z ∈ psdCone d) (z : Point d) (hz : z ∈ feasible S η) :
    operatorNorm S ≤ objective ε z := by
  obtain ⟨hX,hY,h₁,h₂⟩ := (feasible_iff S η z).mp hz
  obtain ⟨ht,htrX,htrY⟩ := trace_bounds_of_feasible S η hη hz
  have hiX : 0 ≤ invH z.2.1 := psd_nonneg (A := invH z.2.1) hX.inv.posSemidef
  have hiY : 0 ≤ invH z.2.2 := psd_nonneg (A := invH z.2.2) hY.inv.posSemidef
  have heX : 0 ≤ η z.2.1 := psd_nonneg (hη _ hX.posSemidef)
  have heY : 0 ≤ η z.2.2 := psd_nonneg (hη _ hY.posSemidef)
  have hu : S ≤ z.1 • (Hermitian.one : H d) := by
    apply le_trans _ h₁
    exact (le_add_of_nonneg_left hiX).trans
      (le_add_of_nonneg_right heY)
  have hl : -z.1 • (Hermitian.one : H d) ≤ S := by
    have hn : -S ≤ z.1 • (Hermitian.one : H d) := by
      apply le_trans _ h₂
      change -S ≤ invH z.2.2+(-S)+η z.2.1
      exact (le_add_of_nonneg_left hiY).trans
        (le_add_of_nonneg_right heX)
    calc
      -z.1 • (Hermitian.one : H d) = -(z.1 • Hermitian.one) := neg_smul z.1 (Hermitian.one : H d)
      _ ≤ S := by simpa only [neg_neg] using neg_le_neg hn
  have hb := operatorNorm_le_of_bounds ht hl hu
  apply hb.trans
  change z.1 ≤ z.1+ε*Hermitian.realTrace (z.2.1+z.2.2)
  rw [realTrace_add]
  exact le_add_of_nonneg_right (mul_nonneg hε (add_nonneg htrX htrY))

lemma cube_zero : Cube (0 : Coordinates N) := fun _ => by norm_num

lemma S_zero (A : Fin N → H d) : S A (0 : Coordinates N) = 0 := by simp [S]

lemma initial_scalar_point [NeZero d] [NeZero N] (A : Fin N → H d) {ν : ℝ} (hν : 0 < ν)
    (hvar : varianceH A ≤ ν • (Hermitian.one : H d)) :
    ∃ z : Point d, z ∈ feasible (S A 0) (eta 384 A 0) ∧
      jointObjective (ν/d) (Real.sqrt ν/(100*N)) ((0 : Coordinates N),z) = (3931/100 : ℝ)*Real.sqrt ν := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hs : 0 < Real.sqrt ν := Real.sqrt_pos.mpr hν
  let a : ℝ := (20*Real.sqrt ν)⁻¹
  have ha : 0 < a := inv_pos.mpr (mul_pos (by norm_num) hs)
  have hh : -(0 : ℝ) • (Hermitian.one : H d) ≤ S A 0 := by rw [S_zero]; simp
  have hh' : S A 0 ≤ (0 : ℝ) • (Hermitian.one : H d) := by rw [S_zero]; simp
  have hb := eta_one_bound (show (0 : ℝ) ≤ 384 by norm_num) A hvar cube_zero
  refine ⟨(0+a⁻¹+(384*ν)*a,a • Hermitian.one,a • Hermitian.one),scalar_feasible _ _ hh hh' hb ha,?_⟩
  change objective (ν/d) (0+a⁻¹+(384*ν)*a,a • Hermitian.one,a • Hermitian.one)+
    (Real.sqrt ν/(100*N))*(∑ i : Fin N,psi ((0 : Coordinates N) i)) = _
  rw [scalar_objective]
  have hpsi : (∑ i : Fin N,psi ((0 : Coordinates N) i)) = N := by simp [psi]
  rw [hpsi]
  dsimp [a]
  rw [inv_inv]
  field_simp [hd,hN,ne_of_gt hs]
  nlinarith [Real.sq_sqrt hν.le]

end CurrentKS.State

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_RealTraceVarianceRank
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

lemma realTrace_variance_rank_one (A : Fin N → H d) (hA : ∀ i,A i ∈ psdCone d)
    (hrank : ∀ i,(A i : Mat d).rank ≤ 1) :
    Hermitian.realTrace (varianceH A)=∑ i,(Hermitian.realTrace (A i))^2 := by
  rw [varianceH,Hermitian.realTrace_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [sandwich_rank_one (A i) _ (hA i) (hrank i),inner_one',Hermitian.realTrace_smul]
  ring

lemma variance_lower [NeZero d] [NeZero N] (A : Fin N → H d)
    (hA : ∀ i,A i ∈ psdCone d) (hrank : ∀ i,(A i : Mat d).rank ≤ 1)
    (htr : ∑ i,Hermitian.realTrace (A i)=1) :
    1/((N:ℝ)*d) ≤ operatorNorm (varianceH A) := by
  have hdpos : (0:ℝ) < d := by exact_mod_cast NeZero.pos d
  have hNpos : (0:ℝ) < N := by exact_mod_cast NeZero.pos N
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) Finset.univ
    (fun _ : Fin N => (1:ℝ)) (fun i => Hermitian.realTrace (A i))
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one,htr] at hcs
  have ht := realTrace_mono (le_operatorNorm_smul_one (varianceH A))
  rw [Hermitian.realTrace_smul,Hermitian.realTrace_one,realTrace_variance_rank_one A hA hrank] at ht
  have hm := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg N : (0:ℝ)≤N)
  apply (div_le_iff₀ (by positivity : (0:ℝ)<N*d)).mpr
  nlinarith

lemma variance_lower_paper [NeZero d] [NeZero N] (A : Fin N → H d)
    (hA : ∀ i,A i ∈ psdCone d) (hrank : ∀ i,(A i : Mat d).rank ≤ 1)
    (htr : ∑ i,Hermitian.realTrace (A i)=1) :
    1/((N:ℝ)*d^2) ≤ operatorNorm (varianceH A) := by
  apply le_trans _ (variance_lower A hA hrank htr)
  have hdpos : (0:ℝ) < d := by exact_mod_cast NeZero.pos d
  have hNpos : (0:ℝ) < N := by exact_mod_cast NeZero.pos N
  apply one_div_le_one_div_of_le (mul_pos hNpos hdpos)
  have hd : (1:ℝ) ≤ d := by exact_mod_cast NeZero.pos d
  exact mul_le_mul_of_nonneg_left (by nlinarith : (d:ℝ) ≤ (d:ℝ)^2) hNpos.le

end
end CurrentKS.State

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_UpperIndex
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalGrid

lemma upperIndex_le (den : ℕ) (test : ℚ → Bool) (k : ℕ) : upperIndex den test k ≤ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [upperIndex]
    split
    · exact ih.trans (Nat.le_succ k)
    · rfl

lemma upperIndex_spec (den : ℕ) (test : ℚ → Bool) (r : ℝ)
    (htest : ∀ k : ℕ,test ((k:ℚ)/den)=true ↔ r ≤ (k:ℝ)/den) (k : ℕ)
    (hk : r ≤ (k:ℝ)/den) :
    r ≤ (upperIndex den test k:ℝ)/den ∧
      (upperIndex den test k:ℝ)/den ≤ r+1/(den:ℝ) ∨ r ≤ 0 ∧ upperIndex den test k=0 := by
  induction k with
  | zero => exact Or.inr ⟨by simpa using hk,rfl⟩
  | succ k ih =>
    by_cases h : test ((k:ℚ)/den)=true
    · simp only [upperIndex,h,↓reduceIte]
      exact ih ((htest k).mp h)
    · have hlt : (k:ℝ)/den < r := lt_of_not_ge (fun he => h ((htest k).mpr he))
      simp only [upperIndex,h,Bool.false_eq_true,↓reduceIte]
      apply Or.inl
      refine ⟨hk,?_⟩
      rw [Nat.cast_add,Nat.cast_one,add_div]
      linarith

theorem upper_spec (den : ℕ) (hden : 0 < den) (test : ℚ → Bool) (r : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (htest : ∀ k : ℕ,test ((k:ℚ)/den)=true ↔ r ≤ (k:ℝ)/den) :
    r ≤ (upper den test:ℝ) ∧ (upper den test:ℝ) ≤ r+1/(den:ℝ) ∧ upper den test ≤ 1 := by
  have hd : (0:ℝ)<den := by exact_mod_cast hden
  have hdq : (0:ℚ)<den := by exact_mod_cast hden
  have hspec := upperIndex_spec den test r htest den (by simpa only [div_self hd.ne'] using hr1)
  have hle : upper den test ≤ 1 := by
    unfold upper
    apply (div_le_one hdq).mpr
    exact_mod_cast upperIndex_le den test den
  have he : (upper den test:ℝ)=(upperIndex den test den:ℝ)/den := by simp [upper]
  refine ⟨?_,?_,hle⟩
  · rcases hspec with hs|hs
    · simpa only [he] using hs.1
    · rw [he,hs.2,Nat.cast_zero,zero_div]
      exact hs.1
  · rcases hspec with hs|hs
    · simpa only [he] using hs.2
    · rw [he,hs.2,Nat.cast_zero,zero_div]
      positivity

end CurrentKS.RationalGrid

namespace CurrentKS.RationalSDP
open Matrix CurrentKS.HermitianCoordinates
open scoped BigOperators

variable {d N : ℕ}

noncomputable section
open CurrentKS.Hermitian CurrentKS.Variational CurrentKS.State
open scoped ComplexOrder MatrixOrder Matrix.Norms.Frobenius

lemma rationalVariance_symm (coords : Fin N → Fin d × Fin d → ℚ) :
    (rationalVariance coords).IsSymm := by
  change (∑ i,realFinDecode d (coords i)*realFinDecode d (coords i)).transpose=_
  rw [Matrix.transpose_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.transpose_mul,(realFinDecode_symm _).eq]

lemma rationalVariance_cast (coords : Fin N → Fin d × Fin d → ℚ) :
    (rationalVariance coords).map (fun q => (q:ℝ)) =
      finRealify ((varianceH (rationalAtoms coords) : H d) : Mat d) := by
  simp only [rationalVariance,cast_matrix_sum,cast_matrix_mul,realFinDecode_cast,
    varianceH,Submodule.coe_sum,finRealify_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [sandwich_val]
  change _=finRealify ((_ : Mat d)*1*(_ : Mat d))
  rw [mul_one,finRealify_mul]
  congr 1

lemma varianceTest_spec (coords : Fin N → Fin d × Fin d → ℚ) (q : ℚ) (hq : 0 ≤ q) :
    varianceTest coords q=true ↔ operatorNorm (varianceH (rationalAtoms coords)) ≤ (q:ℝ) := by
  have hsym : (q • (1 : Matrix (Fin (d+d)) (Fin (d+d)) ℚ)-rationalVariance coords).IsSymm :=
    (Matrix.isSymm_one.smul q).sub (rationalVariance_symm coords)
  rw [varianceTest,Option.isNone_iff_eq_none,KS.W17.rationalNegativeWitness_none_iff_psd _ _ hsym,
    cast_matrix_sub,cast_matrix_smul,cast_matrix_one,rationalVariance_cast]
  rw [← finRealify_one,← finRealify_smul,← finRealify_sub,finRealify_psd]
  change (q:ℝ) • (Hermitian.one : H d)-varianceH (rationalAtoms coords) ∈ psdCone d ↔ _
  rw [mem_psd_iff_nonneg,sub_nonneg]
  constructor
  · exact operatorNorm_le_of_psd_le (varianceH_psd _) (by exact_mod_cast hq)
  · intro h
    exact (le_operatorNorm_smul_one _).trans (scalar_one_mono h)

theorem varianceQuery_spec [NeZero d] [NeZero N] (coords : Fin N → Fin d × Fin d → ℚ)
    (hA : ∀ i,rationalAtoms coords i ∈ psdCone d)
    (hrank : ∀ i,(rationalAtoms coords i : Mat d).rank ≤ 1)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1) :
    let ν := varianceQuery coords
    let ν₀ := operatorNorm (varianceH (rationalAtoms coords))
    0 < ν ∧ ν ≤ 1 ∧ ν₀ ≤ (ν:ℝ) ∧ (ν:ℝ) ≤ (1001/1000:ℝ)*ν₀ := by
  have hd : 0 < d := NeZero.pos d
  have hN : 0 < N := NeZero.pos N
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  let A := rationalAtoms coords
  have hpos := varianceH_pos A hA htr
  have hle := operatorNorm_le_of_psd_le (varianceH_psd A) zero_le_one (by simpa using varianceH_le_one A hA hrank htr)
  have h := CurrentKS.RationalGrid.upper_spec (1000*N*d^2) (by positivity) (varianceTest coords)
    (operatorNorm (varianceH A)) hpos.le hle (fun k => by
      rw [varianceTest_spec coords _ (by positivity)]
      simp only [Rat.cast_div,Rat.cast_natCast]
      rfl)
  have hlow := variance_lower_paper A hA hrank htr
  refine ⟨by exact_mod_cast hpos.trans_le h.1,h.2.2,h.1,?_⟩
  apply h.2.1.trans
  have he : (1:ℝ)/(1000*N*d^2)=(1/1000)*(1/((N:ℝ)*d^2)) := by ring
  push_cast
  rw [he]
  linarith

end
end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_NormPotential
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.State.line_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

lemma norm_le_potential [NeZero d] (A : Fin N → H d)
    (hA : ∀ i,A i∈psdCone d) (htr : ∑ i,Hermitian.realTrace (A i)=1)
    {ε lam ν : ℝ} (hε : 0 < ε) (hεd : ε*d ≤ 1) (hlam : 0 ≤ lam)
    (hν1 : ν ≤ 1) (hvar : varianceH A ≤ ν • (Hermitian.one : H d))
    (x : Coordinates N) (hx : Cube x) : operatorNorm (S A x) ≤ potential 384 ε lam A x := by
  have hp := eta_positive (show (0:ℝ) ≤ 384 by norm_num) A hx
  have hb := S_bounds A hA htr hx
  have hηI : eta 384 A x (Hermitian.one : H d) ≤ (384:ℝ) • (Hermitian.one : H d) := by
    apply (eta_one_bound (show (0:ℝ) ≤ 384 by norm_num) A hvar hx).trans
    exact scalar_one_mono (by linarith)
  obtain ⟨z,hz,_,hm⟩ := normalized_minimizer (S A x) (eta 384 A x) hp hε hεd hb.1 hb.2 hηI
  have hn := feasible_norm_le_objective ε hε.le (S A x) (eta 384 A x) hp z hz
  unfold potential
  rw [value_eq_of_min ε _ _ z hz hm]
  exact hn.trans (le_add_of_nonneg_right (mul_nonneg hlam
    (Finset.sum_nonneg (fun i _ => (psi_bounds (hx i)).1))))

lemma potential_zero_le [NeZero d] [NeZero N] (A : Fin N → H d)
    {ν lam : ℝ} (hν : 0 < ν) (hlam : lam ≤ Real.sqrt ν/(100*N))
    (hvar : varianceH A ≤ ν • (Hermitian.one : H d)) :
    potential 384 (ν/d) lam A 0 ≤ (3931/100:ℝ)*Real.sqrt ν := by
  obtain ⟨z,hz,hzv⟩ := initial_scalar_point A hν hvar
  have hd : (0:ℝ) < d := by exact_mod_cast NeZero.pos d
  have hv := value_le_feasible (ν/d) (div_nonneg hν.le hd.le) _ _
    (eta_positive (show (0:ℝ) ≤ 384 by norm_num) A cube_zero) z hz
  have hm := mul_le_mul_of_nonneg_right hlam
    (Finset.sum_nonneg (fun i (_ : i∈(Finset.univ : Finset (Fin N))) =>
      (psi_bounds (cube_zero i)).1))
  change objective (ν/d) z+(Real.sqrt ν/(100*N))*∑ i,psi ((0:Coordinates N) i)=_ at hzv
  unfold potential
  linarith

end
end CurrentKS.State

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_PenaltyParameter
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Schedule
open CurrentKS.RationalRoot

lemma penaltyParameter_interval {N : ℕ} (hN : 0 < N) {ν : ℚ}
    (hν : 0 < ν) (hν1 : ν ≤ 1) :
    Real.sqrt (ν:ℝ)/(200*N) ≤ (penaltyParameter N ν:ℝ) ∧
      (penaltyParameter N ν:ℝ) ≤ Real.sqrt (ν:ℝ)/(100*N) := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hνr : (0:ℝ) < ν := by exact_mod_cast hν
  have hνr1 : (ν:ℝ) ≤ 1 := by exact_mod_cast hν1
  have hs := upperSqrt_spec ν ν hν hν.le hν1
  have hself : (ν:ℝ) ≤ Real.sqrt (ν:ℝ) := by
    nlinarith [Real.sq_sqrt hνr.le,Real.sqrt_nonneg (ν:ℝ)]
  have hup : (upperSqrt ν ν:ℝ) ≤ 2*Real.sqrt (ν:ℝ) := by linarith
  simp only [penaltyParameter,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast]
  refine ⟨div_le_div_of_nonneg_right hs.1 (by positivity),?_⟩
  have hh := div_le_div_of_nonneg_right hup (show (0:ℝ) ≤ 200*N by positivity)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma penaltyParameter_pos_le {N : ℕ} (hN : 0 < N) {ν : ℚ}
    (hν : 0 < ν) (hν1 : ν ≤ 1) :
    0 < penaltyParameter N ν ∧ penaltyParameter N ν ≤ 1 := by
  have hh := penaltyParameter_interval hN hν hν1
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hn1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hνr : (0:ℝ) < ν := by exact_mod_cast hν
  have hp : (0:ℝ) < penaltyParameter N ν :=
    (div_pos (Real.sqrt_pos.mpr hνr) (by positivity)).trans_le hh.1
  have hu : (penaltyParameter N ν:ℝ) ≤ 1 := by
    apply hh.2.trans
    apply (div_le_one (by positivity)).mpr
    have hs := Real.sqrt_le_one.mpr (show (ν:ℝ) ≤ 1 by exact_mod_cast hν1)
    linarith
  exact ⟨by exact_mod_cast hp,by exact_mod_cast hu⟩

end CurrentKS.Schedule

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_NormalizedRun
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.RationalFace

section
open CurrentKS.Hermitian CurrentKS.State CurrentKS.Variational CurrentKS.Scalar
open CurrentKS.RationalSDP CurrentKS.Schedule CurrentKS.Difference CurrentKS.Descent
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

theorem rationalRun_spec [NeZero d] [NeZero N] (coords : Fin N → Fin d × Fin d → ℚ)
    (hA : ∀ i,rationalAtoms coords i∈psdCone d)
    (hA0 : ∀ i,rationalAtoms coords i≠0)
    (hrank : ∀ i,(rationalAtoms coords i : Mat d).rank ≤ 1)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
    {ν lam : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hlamhi : (lam:ℝ) ≤ Real.sqrt (ν:ℝ)/(100*N))
    (hvar : (∑ i,sandwich (rationalAtoms coords i) (Hermitian.one : H d)) ≤
      (ν:ℝ) • (Hermitian.one : H d)) :
    (∀ i,|rationalRun coords ν lam i|=1) ∧
      operatorNorm (S (rationalAtoms coords) (pointCast (rationalRun coords ν lam))) ≤
        (3931/100:ℝ)*Real.sqrt (ν:ℝ) := by
  let P := StripCube (N:=N) (lam^2/ν)
  let f := fullPotential coords ν lam
  let step := transition coords ν lam
  let x₀ : Fin N → ℚ := freezeAll (lam^2/ν) 0
  let k := fuel (uniformDrop d N ν lam)
  have hp : ∀ x y,P x → step x=some y → P y := by
    intro x y hx hs
    exact (transition_spec coords hA hA0 hrank htr hν hν1 hlam hlam1 hvar x y hx hs).1
  have hd : ∀ x y,P x → step x=some y → f y ≤ f x-(uniformDrop d N ν lam:ℝ) := by
    intro x y hx hs
    exact (transition_spec coords hA hA0 hrank htr hν hν1 hlam hlam1 hvar x y hx hs).2
  have hrq := uniformDrop_pos (N:=N) (d:=d) hν hlam
  have hrr : (0:ℝ) < uniformDrop d N ν lam := by exact_mod_cast hrq
  have he := epsilon_spec (d:=d) hν hν1
  have hε : (0:ℝ) < ((ν/(d:ℚ):ℚ):ℝ) := by exact_mod_cast he.1
  have hεd : ((ν/(d:ℚ):ℚ):ℝ)*(d:ℝ) ≤ 1 := by exact_mod_cast he.2.2
  have hnorm (x : Fin N → ℚ) (hx : P x) :
      operatorNorm (S (rationalAtoms coords) (pointCast x)) ≤ f x := by
    apply norm_le_potential (rationalAtoms coords) hA htr hε hεd
      (by exact_mod_cast hlam.le) (by exact_mod_cast hν1) hvar
    intro i
    change |(x i:ℝ)| ≤ 1
    exact_mod_cast hx.1 i
  have hnon : ∀ x,P x → 0 ≤ f x := by
    intro x hx
    exact (operatorNorm_nonneg _).trans (hnorm x hx)
  have hzero : ∀ i : Fin N, |(0:Fin N → ℚ) i| ≤ 1 := by intro i;norm_num
  have hx₀ : P x₀ := freezeAll_stripCube _ _ hzero
  have hi : f x₀ ≤ (3931/100:ℝ)*Real.sqrt (ν:ℝ) := by
    have hh := potential_zero_le (rationalAtoms coords) (by exact_mod_cast hν) hlamhi hvar
    have hf := fullPotential_freeze coords hA htr hν hν1 hlam.le hvar (0:Fin N → ℚ) hzero
    apply hf.trans
    have hz : pointCast (0:Fin N → ℚ)=0 := by ext i; simp [pointCast]
    change fullPotential coords ν lam 0 ≤ _
    unfold fullPotential
    rw [hz]
    simpa only [Rat.cast_div,Rat.cast_natCast] using hh
  have hi100 : f x₀ ≤ 100 := by
    have hs : Real.sqrt (ν:ℝ) ≤ 1 := (Real.sqrt_le_one).mpr (by exact_mod_cast hν1)
    linarith
  have hk : f x₀ < (k:ℝ)*(uniformDrop d N ν lam:ℝ) :=
    lt_of_le_of_lt hi100 (fuel_spec hrq)
  have ht : step (run step k x₀)=none := run_terminates step P f hrr hnon hp hd k x₀ hx₀ hk
  have hxf : P (run step k x₀) := run_invariant step P hp k x₀ hx₀
  have hv : f (run step k x₀) ≤ f x₀ := run_value_le step P f hp
    (fun x y hx hs => (hd x y hx hs).trans (sub_le_self _ hrr.le)) k x₀ hx₀
  exact ⟨terminal_vertex coords ν lam _ hxf.1 ht,(hnorm _ hxf).trans (hv.trans hi)⟩

lemma scalar_coefficient40 {v w : ℝ} (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hvw : v ≤ (1001/1000:ℝ)*w) :
    (3931/100:ℝ)*Real.sqrt v ≤ 40*Real.sqrt w := by
  have hv2 := Real.sq_sqrt hv
  have hw2 := Real.sq_sqrt hw
  have hs : 0 ≤ Real.sqrt w := Real.sqrt_nonneg _
  nlinarith [Real.sqrt_nonneg v,
    sq_nonneg (40*Real.sqrt w-(3931/100:ℝ)*Real.sqrt v)]

end

open CurrentKS.RationalSDP CurrentKS.Schedule

variable {d N : ℕ}

open CurrentKS.Hermitian CurrentKS.State CurrentKS.Difference
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

theorem normalizedRun_spec_oai [NeZero d] [NeZero N]
    (coords : Fin N → Fin d × Fin d → ℚ)
    (hA : ∀ i,rationalAtoms coords i∈psdCone d)
    (hA0 : ∀ i,rationalAtoms coords i≠0)
    (hrank : ∀ i,(rationalAtoms coords i : Mat d).rank ≤ 1)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1) :
    (∀ i,|normalizedRun coords i|=1) ∧
      operatorNorm (S (rationalAtoms coords) (pointCast (normalizedRun coords))) ≤
        40*Real.sqrt (operatorNorm (varianceH (rationalAtoms coords))) := by
  let ν := varianceQuery coords
  let lam := penaltyParameter N ν
  have hν := varianceQuery_spec coords hA hrank htr
  have hlam := penaltyParameter_pos_le (NeZero.pos N) hν.1 hν.2.1
  have hi := penaltyParameter_interval (NeZero.pos N) hν.1 hν.2.1
  have hvar : varianceH (rationalAtoms coords) ≤ (ν:ℝ) • (Hermitian.one : H d) :=
    (le_operatorNorm_smul_one _).trans (scalar_one_mono hν.2.2.1)
  have hh := rationalRun_spec coords hA hA0 hrank htr hν.1 hν.2.1
    hlam.1 hlam.2 hi.2 hvar
  exact ⟨hh.1,hh.2.trans (scalar_coefficient40 (by exact_mod_cast hν.1.le)
    (operatorNorm_nonneg _) hν.2.2.2)⟩

end CurrentKS.RationalFace

open Matrix

end

end OAI
end

theorem solution : type_of% @OAI.CurrentKS.RationalFace.normalizedRun_spec_oai := @OAI.CurrentKS.RationalFace.normalizedRun_spec_oai
