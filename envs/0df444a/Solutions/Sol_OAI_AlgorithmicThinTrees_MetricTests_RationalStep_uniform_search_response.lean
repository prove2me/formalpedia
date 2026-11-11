-- Prove2me | solution 1 for OAI.AlgorithmicThinTrees.MetricTests.RationalStep.uniform_search_response
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:59:13.357876+00:00
-- url     : https://prove2.me/submissions/bf09f909-ec5f-426d-b3c3-3f2046c27874

import Mathlib
import Definitions.Def_AlgorithmicThinTrees
import Definitions.Def_OAIQ241TT009
import Theorems.Thm_OAI_AlgorithmicThinTrees_MetricTests_finite_continuation_inner_cube
import Theorems.Thm_OAI_AlgorithmicThinTrees_Partitions_finite_chain_response

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_ExactStepDecrease
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalOptimization
noncomputable section
open Set
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma exact_step_decrease (y c v : E) {r : ℝ} (hr : 0 ≤ r)
    (hv : ‖v‖ ≤ 1) (hsep : r ≤ inner ℝ v (c-y)) :
    ‖y+r • v-c‖^2 ≤ ‖y-c‖^2-r^2 := by
  have he : y+r • v-c = (y-c)+r • v := by abel
  rw [he,norm_add_sq_real,real_inner_smul_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
  have hi : inner ℝ (y-c) v ≤ -r := by
    rw [real_inner_comm] at hsep
    have hh : inner ℝ (y-c) v = -(inner ℝ (c-y) v) := by
      rw [← inner_neg_left]
      congr 1
      abel
    linarith
  have hv0 := norm_nonneg v
  have hv2 : ‖v‖^2 ≤ 1 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hi hr
  have ht := mul_le_mul_of_nonneg_left hv2 (sq_nonneg r)
  nlinarith

lemma rounded_step_decrease (y c v y' : E) {r R δ : ℝ}
    (hr : 0 ≤ r) (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hy : ‖y-c‖ ≤ R)
    (hv : ‖v‖ ≤ 1) (hsep : r ≤ inner ℝ v (c-y))
    (hround : ‖y'-(y+r • v)‖ ≤ δ)
    (hsmall : 2*(R+r)*δ+δ^2 ≤ r^2/2) :
    ‖y'-c‖^2 ≤ ‖y-c‖^2-r^2/2 := by
  have hstep := exact_step_decrease y c v hr hv hsep
  have hnorm : ‖y+r • v-c‖ ≤ R+r := by
    have he : y+r • v-c = (y-c)+r • v := by abel
    rw [he]
    calc
      _ ≤ ‖y-c‖+‖r • v‖ := norm_add_le _ _
      _ ≤ R+r := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]; nlinarith
  have hn : ‖y'-c‖ ≤ ‖y+r • v-c‖+δ := by
    calc
      _ = ‖(y+r • v-c)+(y'-(y+r • v))‖ := by congr 1; abel
      _ ≤ ‖y+r • v-c‖+‖y'-(y+r • v)‖ := norm_add_le _ _
      _ ≤ _ := add_le_add_right hround _
  have hn0 := norm_nonneg (y+r • v-c)
  have hn' := sq_le_sq₀ (norm_nonneg (y'-c)) (add_nonneg hn0 hδ) |>.mpr hn
  have hh := mul_le_mul hnorm (le_refl δ) hδ (add_nonneg hR hr)
  nlinarith

lemma separating_margin (K : Set E) (c y v : E) {r b : ℝ}
    (hr : 0 ≤ r) (hball : Metric.closedBall c r ⊆ K)
    (hv : ‖v‖ = 1) (hsep : ∀ z ∈ K, b ≤ inner ℝ v z)
    (hy : inner ℝ v y ≤ b) : r ≤ inner ℝ v (c-y) := by
  have hz : c-r • v ∈ Metric.closedBall c r := by
    rw [Metric.mem_closedBall,dist_eq_norm]
    have he : c-r • v-c = -(r • v) := by abel
    rw [he,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr,hv,mul_one]
  have hs := hsep _ (hball hz)
  rw [inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,hv] at hs
  rw [inner_sub_right]
  nlinarith

end
end CurrentKS.RationalOptimization

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
attribute [-simp] _root_.OAI.KS.W17.PivotHistory.restore_push _root_.OAI.KS.W17.schurWitnessLift_zero_pivot
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
attribute [-simp] _root_.OAI.KS.W17.PivotHistory.restore_push _root_.OAI.KS.W17.schurEntryExpr_eval _root_.OAI.KS.W17.schurTail_zero_pivot _root_.OAI.KS.W17.schurWitnessLift_zero_pivot
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
attribute [-simp] _root_.OAI.KS.W17.PivotHistory.restore_push _root_.OAI.KS.W17.schurEntryExpr_eval _root_.OAI.KS.W17.schurTail_zero_pivot _root_.OAI.KS.W17.schurWitnessLift_zero_pivot
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
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_Pencil
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open Matrix
open scoped BigOperators

variable {n m : ℕ}

lemma Pencil.eval_symmetric (B : Pencil n m) (y : Fin n → ℚ) : (B.eval y).IsSymm := by
  unfold Pencil.eval
  apply Matrix.IsSymm.ext
  intro i j
  simp only [Matrix.add_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  rw [B.symmetric_constant.apply]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [(B.symmetric_coeff k).apply]

lemma Pencil.cast_eval (B : Pencil n m) (y : Fin n → ℚ) :
    (B.eval y).map (fun x => (x : ℝ)) = B.realEval (fun i => (y i : ℝ)) := by
  ext i j
  simp [Pencil.eval,Pencil.realEval,Matrix.sum_apply,Rat.cast_sum]

lemma Pencil.quadratic_eval (B : Pencil n m) (v : Fin m → ℚ) (y : Fin n → ℚ) :
    KS.W17.psdCutEval v (B.eval y) = B.normal v ⬝ᵥ y - B.offset v := by
  unfold Pencil.normal Pencil.offset
  simp only [KS.W17.psdCutEval,Pencil.eval,Matrix.add_mulVec,
    Matrix.sum_mulVec,Matrix.smul_mulVec,dotProduct_add,dotProduct_sum,dotProduct_smul,
    smul_eq_mul]
  simp only [dotProduct,neg_mul,Finset.sum_neg_distrib]
  rw [show (∑ i, y i * (∑ j,v j*(B.coeff i *ᵥ v) j)) =
      ∑ i, (∑ j,v j*(B.coeff i *ᵥ v) j)*y i by
    apply Finset.sum_congr rfl; intro i _; ring]
  ring

lemma Pencil.quadratic_realEval (B : Pencil n m) (v : Fin m → ℚ) (y : Fin n → ℝ) :
    KS.W17.psdCutEvalReal v (B.realEval y) =
      (fun i => (B.normal v i : ℝ)) ⬝ᵥ y - (B.offset v : ℝ) := by
  unfold Pencil.realEval
  simp only [KS.W17.psdCutEvalReal,Matrix.add_mulVec,Matrix.sum_mulVec,Matrix.smul_mulVec,
    dotProduct_add,dotProduct_sum,dotProduct_smul,smul_eq_mul]
  have hc : (fun i => (v i : ℝ)) ⬝ᵥ
      (B.constant.map (fun x : ℚ => (x : ℝ)) *ᵥ (fun i => (v i : ℝ))) =
      (B.offset v : ℝ) := by
    simp [Pencil.offset,KS.W17.psdCutEval,dotProduct,Matrix.mulVec,Rat.cast_sum]
  have hi (i : Fin n) : (fun j => (v j : ℝ)) ⬝ᵥ
      ((B.coeff i).map (fun x : ℚ => (x : ℝ)) *ᵥ (fun j => (v j : ℝ))) =
      -(B.normal v i : ℝ) := by
    simp [Pencil.normal,KS.W17.psdCutEval,dotProduct,Matrix.mulVec,Rat.cast_sum]
  rw [hc]
  simp_rw [hi]
  simp only [dotProduct,mul_neg,Finset.sum_neg_distrib]
  rw [show (∑ i, y i * (B.normal v i : ℝ)) = ∑ i, (B.normal v i : ℝ)*y i by
    apply Finset.sum_congr rfl; intro i _; ring]
  ring

lemma Pencil.witness_none_iff (B : Pencil n m) (y : Fin n → ℚ) :
    B.witness y = none ↔ (B.realEval (fun i => (y i : ℝ))).PosSemidef := by
  rw [Pencil.witness,KS.W17.rationalNegativeWitness_none_iff_psd _ _ (B.eval_symmetric y),
    B.cast_eval]

lemma Pencil.witness_some (B : Pencil n m) (y : Fin n → ℚ) (v : Fin m → ℚ)
    (hv : B.witness y = some v) :
    B.offset v < B.normal v ⬝ᵥ y ∧
      ∀ z : Fin n → ℝ, (B.realEval z).PosSemidef →
        (fun i => (B.normal v i : ℝ)) ⬝ᵥ z ≤ (B.offset v : ℝ) := by
  constructor
  · have h := KS.W17.rationalNegativeWitness_sound _ _ (B.eval_symmetric y) v hv
    have h' : 0 < KS.W17.psdCutEval v (B.eval y) := neg_pos.mpr h
    rw [B.quadratic_eval] at h'
    linarith
  · intro z hz
    have h := KS.W17.psdCutEvalReal_nonpos v _ hz
    rw [B.quadratic_realEval] at h
    linarith

lemma Pencil.normal_ne_zero (B : Pencil n m) (y : Fin n → ℚ) (v : Fin m → ℚ)
    (hv : B.witness y = some v) (z : Fin n → ℝ) (hz : (B.realEval z).PosSemidef) :
    B.normal v ≠ 0 := by
  intro hzero
  obtain ⟨h₁,h₂⟩ := B.witness_some y v hv
  have h₂ := h₂ z hz
  rw [hzero,zero_dotProduct] at h₁
  have hzero' : (fun i => (B.normal v i : ℝ)) = 0 := by funext i; simp [hzero]
  rw [hzero',zero_dotProduct] at h₂
  exact (not_lt_of_ge h₂) (by exact_mod_cast h₁)

lemma Pencil.central_cut (B : Pencil n m) (y : Fin n → ℚ) (v : Fin m → ℚ)
    (hv : B.witness y = some v) (z : Fin n → ℝ) (hz : (B.realEval z).PosSemidef) :
    (fun i => (B.normal v i : ℝ)) ⬝ᵥ (z - fun i => (y i : ℝ)) ≤ 0 := by
  obtain ⟨h₁,h₂⟩ := B.witness_some y v hv
  have h₂ := h₂ z hz
  have h₁' : (B.offset v : ℝ) <
      (fun i => (B.normal v i : ℝ)) ⬝ᵥ (fun i => (y i : ℝ)) := by
    simpa [dotProduct,Rat.cast_sum] using (Rat.cast_lt (K := ℝ)).mpr h₁
  rw [dotProduct_sub]
  linarith

end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_RealVector
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open scoped BigOperators RealInnerProductSpace
open Set

variable {n m : ℕ}

lemma norm_le_sum_abs (v : EuclideanSpace ℝ (Fin n)) : ‖v‖ ≤ ∑ i, |v i| := by
  apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun i _ => abs_nonneg _))).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  simpa only [sq_abs] using Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
    (f := fun i => |v i|) (fun i _ => abs_nonneg _)

lemma l1_bounds (a : Fin n → ℚ) :
    ‖realVector a‖ ≤ (l1 a : ℝ) ∧ (l1 a : ℝ) ≤ (n+1 : ℝ)*‖realVector a‖ := by
  have hcast : (l1 a : ℝ) = ∑ i, |realVector a i| := by
    simp [l1,realVector,Rat.cast_sum]
  rw [hcast]
  refine ⟨norm_le_sum_abs _,?_⟩
  calc
    _ ≤ ∑ _i : Fin n, ‖realVector a‖ := Finset.sum_le_sum (fun i _ => by
      simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le (realVector a) i))
    _ = (n : ℝ)*‖realVector a‖ := by simp
    _ ≤ _ := by nlinarith [norm_nonneg (realVector a)]

lemma l1_pos {a : Fin n → ℚ} (ha : a ≠ 0) : 0 < l1 a := by
  have ha' : realVector a ≠ 0 := by
    intro h
    apply ha
    funext i
    have hh := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x i) h
    simp only [realVector,PiLp.toLp_apply,PiLp.zero_apply,Rat.cast_eq_zero] at hh
    exact hh
  have hp := norm_pos_iff.mpr ha'
  exact_mod_cast lt_of_lt_of_le hp (l1_bounds a).1

lemma roundScalar_error (ρ x : ℚ) (hρ : 0 < ρ) : |roundScalar ρ x-x| ≤ ρ := by
  have h₁ := Int.floor_le (x/ρ)
  have h₂ := Int.lt_floor_add_one (x/ρ)
  have hlow : roundScalar ρ x ≤ x := by
    dsimp [roundScalar]
    have := mul_le_mul_of_nonneg_left h₁ hρ.le
    rwa [mul_div_cancel₀ _ hρ.ne'] at this
  have hhigh : x < roundScalar ρ x+ρ := by
    dsimp [roundScalar]
    have := mul_lt_mul_of_pos_left h₂ hρ
    rw [mul_div_cancel₀ _ hρ.ne'] at this
    linarith
  rw [abs_of_nonpos (sub_nonpos.mpr hlow)]
  linarith

lemma realVector_round_error (ρ : ℚ) (hρ : 0 < ρ) (y : Fin n → ℚ) :
    ‖realVector (roundVector ρ y)-realVector y‖ ≤ (n+1 : ℝ)*(ρ : ℝ) := by
  calc
    _ ≤ ∑ i, |(realVector (roundVector ρ y)-realVector y) i| := norm_le_sum_abs _
    _ ≤ ∑ _i : Fin n, (ρ : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have h := roundScalar_error ρ (y i) hρ
      simpa only [realVector,roundVector,PiLp.sub_apply,PiLp.toLp_apply,Rat.cast_sub,
        Rat.cast_abs] using (Rat.cast_le (K := ℝ)).mpr h
    _ = (n : ℝ)*(ρ : ℝ) := by simp
    _ ≤ _ := by
      have hp : 0 < (ρ : ℝ) := by exact_mod_cast hρ
      nlinarith

lemma normalized_norm_le_one (a : Fin n → ℚ) : ‖normalized a‖ ≤ 1 := by
  by_cases ha : a=0
  · simp [normalized,l1,ha,realVector]
  have hq : 0 < (l1 a : ℝ) := by exact_mod_cast l1_pos ha
  rw [normalized,norm_smul,Real.norm_eq_abs,abs_neg,abs_inv,abs_of_pos hq]
  exact (inv_mul_le_iff₀ hq).mpr (by simpa only [mul_one] using (l1_bounds a).1)

lemma normalized_margin (K : Set (EuclideanSpace ℝ (Fin n))) (c : EuclideanSpace ℝ (Fin n))
    (y a : Fin n → ℚ) {r : ℝ} (hr : 0 ≤ r) (ha : a ≠ 0)
    (hball : Metric.closedBall c r ⊆ K)
    (hsep : ∀ z ∈ K, inner ℝ (realVector a) (z-realVector y) ≤ 0) :
    r/(n+1) ≤ inner ℝ (normalized a) (c-realVector y) := by
  have hq : 0 < (l1 a : ℝ) := by exact_mod_cast l1_pos ha
  have ha0 : realVector a ≠ 0 := by
    intro h
    have han := (l1_bounds a).2
    rw [h,norm_zero,mul_zero] at han
    linarith
  have hnorm : 0 < ‖realVector a‖ := norm_pos_iff.mpr ha0
  let v := (-‖realVector a‖⁻¹) • realVector a
  have hv : ‖v‖ = 1 := by
    dsimp [v]
    rw [norm_smul,Real.norm_eq_abs,abs_neg,abs_inv,abs_of_pos hnorm,inv_mul_cancel₀ hnorm.ne']
  have hsep' : ∀ z ∈ K, inner ℝ v (realVector y) ≤ inner ℝ v z := by
    intro z hz
    have hh := hsep z hz
    rw [inner_sub_right] at hh
    dsimp [v]
    rw [real_inner_smul_left,real_inner_smul_left]
    exact mul_le_mul_of_nonpos_left (by linarith) (neg_nonpos.mpr (inv_nonneg.mpr hnorm.le))
  have hm := CurrentKS.RationalOptimization.separating_margin K c (realVector y) v hr hball hv hsep' le_rfl
  have hn : normalized a = (‖realVector a‖/(l1 a : ℝ)) • v := by
    dsimp [normalized,v]
    rw [smul_smul]
    congr 1
    field_simp
  rw [hn,real_inner_smul_left]
  have hrn : (1 : ℝ)/(n+1) ≤ ‖realVector a‖/(l1 a : ℝ) := by
    apply (div_le_div_iff₀ (by positivity : (0:ℝ)<n+1) hq).mpr
    simpa only [one_mul,mul_comm] using (l1_bounds a).2
  calc
    r/(n+1) = ((1:ℝ)/(n+1))*r := by ring
    _ ≤ (‖realVector a‖/(l1 a : ℝ))*inner ℝ v (c-realVector y) :=
      mul_le_mul hrn hm hr (div_nonneg hnorm.le hq.le)

lemma realVector_step (y a : Fin n → ℚ) (step : ℚ) :
    realVector (fun i => y i-step*a i/l1 a) = realVector y+(step : ℝ) • normalized a := by
  ext i
  simp [realVector,normalized,Rat.cast_sub,Rat.cast_mul,div_eq_mul_inv]
  ring

end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_Feasible
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open scoped BigOperators RealInnerProductSpace
open Set

variable {n m : ℕ}

lemma Pencil.next_eq_self (B : Pencil n m) (step mesh : ℚ) (y : Fin n → ℚ)
    (hy : B.witness y=none) : B.next step mesh y=y := by simp [Pencil.next,hy]

lemma Pencil.next_decrease (B : Pencil n m) (step mesh : ℚ) (y : Fin n → ℚ)
    (c : EuclideanSpace ℝ (Fin n)) {r R : ℝ}
    (hr : 0 < r) (hR : 0 ≤ R) (hmesh : 0 < mesh)
    (hstep : (step : ℝ)=r/(n+1))
    (hball : Metric.closedBall c r ⊆ B.feasible)
    (hsmall : 2*(R+step)*((n+1)*mesh)+((n+1)*mesh)^2 ≤ (step : ℝ)^2/2)
    (hy : ‖realVector y-c‖ ≤ R) (hfail : B.witness y ≠ none) :
    ‖realVector (B.next step mesh y)-c‖^2 ≤ ‖realVector y-c‖^2-(step : ℝ)^2/2 := by
  obtain ⟨v,hv⟩ := Option.ne_none_iff_exists'.mp hfail
  have hc : c ∈ B.feasible := hball (Metric.mem_closedBall_self hr.le)
  have ha := B.normal_ne_zero y v hv c hc
  have hm := normalized_margin B.feasible c y (B.normal v) hr.le ha hball
    (fun z hz => by
      have h := B.central_cut y v hv z hz
      change (∑ i : Fin n, (z i-(y i : ℝ))*(B.normal v i : ℝ)) ≤ 0
      simpa only [dotProduct,Pi.sub_apply,mul_comm] using h)
  have hround := realVector_round_error mesh hmesh
    (fun i => y i-step*B.normal v i/l1 (B.normal v))
  rw [realVector_step] at hround
  have hp : 0 ≤ (step : ℝ) := by rw [hstep]; positivity
  have hδ : 0 ≤ (n+1 : ℝ)*(mesh : ℝ) := by positivity
  rw [Pencil.next,hv]
  exact CurrentKS.RationalOptimization.rounded_step_decrease _ c _ _ hp hR hδ hy
    (normalized_norm_le_one _) (hstep ▸ hm) hround hsmall

theorem Pencil.search_feasible (B : Pencil n m) (step mesh : ℚ) (y : Fin n → ℚ)
    (c : EuclideanSpace ℝ (Fin n)) {r R : ℝ}
    (hr : 0 < r) (hR : 0 ≤ R) (hmesh : 0 < mesh)
    (hstep : (step : ℝ)=r/(n+1))
    (hball : Metric.closedBall c r ⊆ B.feasible)
    (hsmall : 2*(R+step)*((n+1)*mesh)+((n+1)*mesh)^2 ≤ (step : ℝ)^2/2)
    (hy : ‖realVector y-c‖ ≤ R) (T : ℕ) (hT : R^2 < T*(step : ℝ)^2/2) :
    B.witness ((B.next step mesh)^[T] y)=none := by
  have hp : 0 < (step : ℝ) := by rw [hstep]; positivity
  have hbound : ∀ k : ℕ,
      B.witness ((B.next step mesh)^[k] y)=none ∨
      ‖realVector ((B.next step mesh)^[k] y)-c‖^2 ≤ R^2-k*(step : ℝ)^2/2 := by
    intro k
    induction k with
    | zero =>
      right
      simpa using (sq_le_sq₀ (norm_nonneg _) hR).mpr hy
    | succ k ih =>
      rcases ih with hh|hh
      · left
        rw [Function.iterate_succ_apply',B.next_eq_self _ _ _ hh]
        exact hh
      · by_cases ha : B.witness ((B.next step mesh)^[k] y)=none
        · left
          rw [Function.iterate_succ_apply',B.next_eq_self _ _ _ ha]
          exact ha
        · right
          have hdist : ‖realVector ((B.next step mesh)^[k] y)-c‖ ≤ R := by
            apply (sq_le_sq₀ (norm_nonneg _) hR).mp
            calc
              _ ≤ R^2-k*(step : ℝ)^2/2 := hh
              _ ≤ R^2 := sub_le_self _ (by positivity)
          have hd := B.next_decrease step mesh ((B.next step mesh)^[k] y) c hr hR hmesh
            hstep hball hsmall hdist ha
          rw [Function.iterate_succ_apply']
          push_cast
          linarith
  rcases hbound T with h|h
  · exact h
  · have hn := sq_nonneg ‖realVector ((B.next step mesh)^[T] y)-c‖
    linarith

end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_SearchStep
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open scoped BigOperators RealInnerProductSpace
open Set

variable {n m : ℕ}

lemma searchStep_pos {r : ℚ} (hr : 0 < r) : 0 < searchStep n r := by
  unfold searchStep
  positivity

lemma searchMesh_pos {r R : ℚ} (hr : 0 < r) (hR : 0 ≤ R) : 0 < searchMesh n r R := by
  have hs := searchStep_pos (n := n) hr
  unfold searchMesh
  positivity

lemma mesh_error_small {s R : ℝ} (hs : 0 < s) (_hs1 : s ≤ 1) (hR : 0 ≤ R) :
    2*(R+s)*(s^2/(16*(R+s+1)))+(s^2/(16*(R+s+1)))^2 ≤ s^2/2 := by
  have hden : 0 < 16*(R+s+1) := by positivity
  have hδ : 0 ≤ s^2/(16*(R+s+1)) := by positivity
  have hfirst : 2*(R+s)*(s^2/(16*(R+s+1))) ≤ s^2/8 := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hden (by norm_num : (0:ℝ)<8)).mpr
    nlinarith [sq_nonneg s]
  have hδs : s^2/(16*(R+s+1)) ≤ s/16 := by
    apply (div_le_div_iff₀ hden (by norm_num : (0:ℝ)<16)).mpr
    nlinarith [mul_nonneg hs.le hR]
  have hδsq := pow_le_pow_left₀ hδ hδs 2
  nlinarith [sq_nonneg s]

lemma searchMesh_small {r R : ℚ} (hr : 0 < r) (hr1 : r ≤ 1) (hR : 0 ≤ R) :
    2*((R : ℝ)+searchStep n r)*((n+1)*(searchMesh n r R : ℝ))+
      ((n+1)*(searchMesh n r R : ℝ))^2 ≤ (searchStep n r : ℝ)^2/2 := by
  have hn : (n+1 : ℝ) ≠ 0 := by positivity
  have hs : 0 < (searchStep n r : ℝ) := by exact_mod_cast searchStep_pos (n := n) hr
  have hs1' : searchStep n r ≤ 1 := by
    apply (div_le_one (by positivity : (0:ℚ)<n+1)).mpr
    exact hr1.trans (le_add_of_nonneg_left (Nat.cast_nonneg n))
  have hs1 : (searchStep n r : ℝ) ≤ 1 := by exact_mod_cast hs1'
  have hR' : 0 ≤ (R:ℝ) := by exact_mod_cast hR
  have he : (n+1)*(searchMesh n r R : ℝ) =
      (searchStep n r : ℝ)^2/(16*((R:ℝ)+searchStep n r+1)) := by
    simp only [searchMesh,Rat.cast_div,Rat.cast_pow,Rat.cast_mul,Rat.cast_add,
      Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_one]
    field_simp
  rw [he]
  exact mesh_error_small hs hs1 hR'

lemma searchFuel_suffices {r R : ℚ} (hr : 0 < r) (_hR : 0 ≤ R) :
    (R:ℝ)^2 < (searchFuel n r R : ℝ)*(searchStep n r : ℝ)^2/2 := by
  have hs : 0 < searchStep n r := searchStep_pos hr
  have hc := Nat.le_ceil (4*R^2/(searchStep n r)^2)
  have hh : 2*R^2/(searchStep n r)^2 < (searchFuel n r R : ℚ) := by
    unfold searchFuel
    push_cast
    have := div_nonneg (sq_nonneg R) (sq_nonneg (searchStep n r))
    simp only [mul_div_assoc] at hc ⊢
    linarith
  have hmul := (div_lt_iff₀ (pow_pos hs 2)).mp hh
  have hcast : 2*(R:ℝ)^2 < (searchFuel n r R : ℝ)*(searchStep n r : ℝ)^2 := by
    exact_mod_cast hmul
  linarith

theorem Pencil.search_accepts (B : Pencil n m) (r R : ℚ) (y : Fin n → ℚ)
    (c : EuclideanSpace ℝ (Fin n)) (hr : 0 < r) (hr1 : r ≤ 1) (hR : 0 ≤ R)
    (hball : Metric.closedBall c (r:ℝ) ⊆ B.feasible)
    (hy : ‖realVector y-c‖ ≤ (R:ℝ)) :
    B.witness (B.search r R y)=none := by
  apply B.search_feasible (searchStep n r) (searchMesh n r R) y c
    (by exact_mod_cast hr) (by exact_mod_cast hR) (searchMesh_pos hr hR)
    (by simp [searchStep]) hball (searchMesh_small hr hr1 hR) hy
    (searchFuel n r R) (searchFuel_suffices hr hR)

end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Duality
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uI uJ uV uI2 uI3 uV2 uW uJ2 uV3 uE2 uT uJ3 uH uI4

section

namespace StrongThinTree.Duality
noncomputable section
open Finset
open scoped Classical
variable {E : Type uE} {I : Type uI} [AddCommGroup E] [Module ℝ E] [Fintype I]

omit [AddCommGroup E] [Module ℝ E] in
lemma strictUpperImage_isOpen (S : Set E) (F : I → E → ℝ) :
    IsOpen (strictUpperImage S F) := by
  have he : strictUpperImage S F = ⋃x ∈ S, ⋂i, {v : I → ℝ | F i x < v i} := by
    ext v; simp [strictUpperImage]
  rw [he]
  exact isOpen_iUnion (fun x => isOpen_iUnion (fun _ => isOpen_iInter_of_finite
    (fun i => isOpen_lt continuous_const (continuous_apply i))))

omit [Fintype I] in
lemma strictUpperImage_convex (S : Set E) (F : I → E → ℝ)
    (hS : Convex ℝ S) (hF : ∀i, ConvexOn ℝ S (F i)) :
    Convex ℝ (strictUpperImage S F) := by
  intro u hu v hv a b ha hb hab
  obtain ⟨x,hx,hxu⟩ := hu
  obtain ⟨y,hy,hyv⟩ := hv
  refine ⟨a • x+b • y,hS hx hy ha hb hab,?_⟩
  intro i
  have hf := (hF i).2 hx hy ha hb hab
  change F i (a • x+b • y) < a*u i+b*v i
  change F i (a • x+b • y) ≤ a*F i x+b*F i y at hf
  have hlt : a*F i x+b*F i y < a*u i+b*v i := by
    by_cases ha0 : a=0
    · have hb1 : b=1 := by linarith
      simpa [ha0,hb1] using hyv i
    · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left (hxu i) hapos)
        (mul_le_mul_of_nonneg_left (hyv i).le hb)
  exact hf.trans_lt hlt

lemma functional_coordinates (l : (I → ℝ) →L[ℝ] ℝ) (v : I → ℝ) :
    l v = ∑i, l (Pi.single i 1)*v i := by
  have he : v=∑i, v i • Pi.single i (1:ℝ) := by
    funext j
    simp [Pi.single_apply]
  calc
    l v = l (∑i, v i • Pi.single i (1:ℝ)) := congrArg l he
    _ = ∑i, l (Pi.single i 1)*v i := by
      rw [map_sum]
      apply sum_congr rfl
      intro i _
      rw [map_smul]
      simp only [smul_eq_mul,mul_comm]

lemma convex_alternative (S : Set E) (hS : Convex ℝ S) (hne : S.Nonempty)
    (F : I → E → ℝ) (hF : ∀i, ConvexOn ℝ S (F i))
    (hinfeasible : ¬∃x ∈ S, ∀i, F i x < 0) :
    ∃w : I → ℝ, (∀i, 0 ≤ w i) ∧ (∑i, w i)=1 ∧
      ∀x ∈ S, 0 ≤ ∑i, w i*F i x := by
  have hzero : (0:I → ℝ) ∉ strictUpperImage S F := hinfeasible
  obtain ⟨l,hl⟩ := geometric_hahn_banach_point_open (strictUpperImage_convex S F hS hF)
    (strictUpperImage_isOpen S F) hzero
  simp only [map_zero] at hl
  let w : I → ℝ := fun i => l (Pi.single i 1)
  obtain ⟨x₀,hx₀⟩ := hne
  let v₀ : I → ℝ := fun i => F i x₀+1
  have hv₀ : v₀ ∈ strictUpperImage S F := ⟨x₀,hx₀,fun i => by dsimp [v₀] <;> linarith⟩
  have hlv : 0 < l v₀ := hl v₀ hv₀
  have hw : ∀i, 0 ≤ w i := by
    intro i
    by_contra hh
    have hi : w i < 0 := lt_of_not_ge hh
    let t := (l v₀+1)/(-w i)
    have ht : 0 ≤ t := div_nonneg (by linarith only [hlv]) (neg_pos.mpr hi).le
    have hv : v₀+t • Pi.single i 1 ∈ strictUpperImage S F := by
      refine ⟨x₀,hx₀,?_⟩
      intro j
      change F j x₀ < v₀ j+t*((Pi.single i (1:ℝ) : I → ℝ) j)
      have hj : 0 ≤ ((Pi.single i (1:ℝ) : I → ℝ) j) := by simp [Pi.single_apply]; split_ifs <;> norm_num
      exact (show F j x₀ < v₀ j by dsimp [v₀] <;> linarith).trans_le (le_add_of_nonneg_right (mul_nonneg ht hj))
    have hh := hl _ hv
    rw [map_add,map_smul] at hh
    change 0 < l v₀+t*w i at hh
    have hid : t*w i=-(l v₀+1) := by dsimp [t]; field_simp [ne_of_lt hi]
    linarith only [hh,hid]
  let W := ∑i, w i
  have hW : 0 < W := by
    have hWnon : 0 ≤ W := sum_nonneg (fun i _ => hw i)
    by_contra hh
    have hW0 : W=0 := le_antisymm (le_of_not_gt hh) hWnon
    have hw0 : ∀i, w i=0 := fun i => (sum_eq_zero_iff_of_nonneg (fun i _ => hw i)).mp hW0 i (mem_univ i)
    rw [functional_coordinates] at hlv
    have hz : ∑i, l (Pi.single i 1)*v₀ i=0 := by
      change (∑i, w i*v₀ i)=0
      simp [hw0]
    linarith only [hlv,hz]
  have hbound : ∀x ∈ S, 0 ≤ ∑i, w i*F i x := by
    intro x hx
    apply le_of_forall_pos_lt_add
    intro ε hε
    have heps : 0 < ε/W := div_pos hε hW
    have hv : (fun i => F i x+ε/W) ∈ strictUpperImage S F :=
      ⟨x,hx,fun i => lt_add_of_pos_right _ heps⟩
    have hh := hl _ hv
    rw [functional_coordinates] at hh
    change 0 < ∑i, w i*(F i x+ε/W) at hh
    simp only [mul_add,sum_add_distrib,←sum_mul] at hh
    have heq : W*(ε/W)=ε := by field_simp
    change 0 < (∑i, w i*F i x)+W*(ε/W) at hh
    rwa [heq] at hh
  refine ⟨fun i => w i/W,fun i => div_nonneg (hw i) hW.le,?_,?_⟩
  · rw [←sum_div]
    exact div_self hW.ne'
  · intro x hx
    simp only [div_mul_eq_mul_div,←sum_div]
    exact div_nonneg (hbound x hx) hW.le
end
end StrongThinTree.Duality

namespace StrongThinTree.ShortcutDual
noncomputable section
open Matrix Finset Filter Topology
open scoped Classical MatrixOrder Matrix.Norms.L2Operator
variable {V : Type uV3} {E : Type uE2} {T : Type uT} {J : Type uJ3} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype T] [Fintype J]

omit [DecidableEq V] in
lemma trace_outer_mul (v : V → ℝ) (D : Matrix V V ℝ) :
    (vecMulVec v v * D).trace = v ⬝ᵥ (D *ᵥ v) := by
  rw [vecMulVec_mul,trace_vecMulVec,dotProduct_comm,dotProduct_mulVec]

end
end StrongThinTree.ShortcutDual

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_ShortcutDuality
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.Partitions.mem_crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace StrongThinTree.MultiGraph
noncomputable section
open Matrix Finset StrongThinTree.Geometry
open scoped Classical MatrixOrder Matrix.Norms.L2Operator
variable {n m h : ℕ} (G : MultiGraph n m)

lemma eval_incidence (x : Fin n → ℝ) (e : Fin m) :
    (∑v, x v*G.incidence e v)=x (G.left e)-x (G.right e) := by
  simp [incidence,point,Pi.sub_apply,mul_sub,sum_sub_distrib,Pi.single_apply,mul_ite]

end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_MatrixDomain
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV

section

noncomputable section
open Matrix Finset
open scoped MatrixOrder Matrix.Norms.Elementwise
namespace StrongThinTree
variable {V : Type uV} [Fintype V] [DecidableEq V]
omit [DecidableEq V] in
lemma isClosed_matrixAbove (A : Matrix V V ℝ) : IsClosed {X : Matrix V V ℝ | A ≤ X} :=
  isClosed_psd.preimage (continuous_id.sub continuous_const)
end StrongThinTree

end
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_HierarchyBounds
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Finset Filter
open scoped Topology
namespace StrongThinTree.ShortcutNumeric
open MultiGraph.Hierarchy

lemma eventually_const_mul_rpow_le_rpow (c : ℝ) {a b : ℝ} (hab : a < b) :
    ∀ᶠ x : ℝ in atTop, c*x^a ≤ x^b := by
  have hh := (tendsto_rpow_atTop (sub_pos.mpr hab)).eventually (eventually_ge_atTop c)
  filter_upwards [hh,eventually_gt_atTop (0:ℝ)] with x hx hxp
  calc
    c*x^a ≤ x^(b-a)*x^a := mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg hxp.le _)
    _ = x^b := by rw [←Real.rpow_add hxp]; congr 1; ring

end StrongThinTree.ShortcutNumeric

end
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_MatrixBound
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric matrix bound. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder

variable {n m d : ℕ}

lemma sqrt_gram {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z.PosSemidef) :
    (CFC.sqrt Z)ᵀ*CFC.sqrt Z=Z := by
  rw [isHermitian_iff_isSymm.mp (CFC.sqrt_nonneg Z).posSemidef.isHermitian]
  exact CFC.sqrt_mul_sqrt_self Z hZ.nonneg

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_CenteredMatrices
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.Partitions.mem_crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Centered matrices. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder

variable {n m : ℕ}

lemma ones_dot (x : Fin n → ℝ) : ones n ⬝ᵥ x=∑i, x i := by
  simp [ones,dotProduct]

lemma constantProjection_mulVec (x : Fin n → ℝ) :
    constantProjection n *ᵥ x=((∑i, x i)/(n:ℝ)) • ones n := by
  ext j
  simp [constantProjection,mulVec,dotProduct,Matrix.smul_apply,vecMulVec,ones,div_eq_mul_inv,Finset.sum_mul,mul_comm]

lemma centering_mulVec (x : Fin n → ℝ) :
    centering n *ᵥ x=x-((∑i, x i)/(n:ℝ)) • ones n := by
  rw [centering,sub_mulVec,one_mulVec,constantProjection_mulVec]

lemma centering_mulVec_of_sum_zero {x : Fin n → ℝ} (hx : ∑i, x i=0) :
    centering n *ᵥ x=x := by
  simp only [centering_mulVec,hx,zero_div,zero_smul,sub_zero]

lemma constantProjection_ones (hn : 0 < n) : constantProjection n *ᵥ ones n=ones n := by
  rw [constantProjection_mulVec]
  simp only [ones,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  rw [div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)),one_smul]

lemma centering_ones (hn : 0 < n) : centering n *ᵥ ones n=0 := by
  rw [centering,sub_mulVec,one_mulVec,constantProjection_ones hn,sub_self]

lemma centered_psd {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.PosSemidef) : (centered D).PosSemidef := by
  have hh := hD.mul_mul_conjTranspose_same (centering n)
  simpa only [centered,conjTranspose_eq_transpose_of_trivial,centering_symmetric] using hh

lemma centered_ones (hn : 0 < n) (D : Matrix (Fin n) (Fin n) ℝ) : centered D *ᵥ ones n=0 := by
  simp only [centered,←mulVec_mulVec,centering_ones hn,mulVec_zero]

lemma qform_centered (D : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    qform (centered D) x=qform D (centering n *ᵥ x) := by
  unfold centered qform
  rw [←mulVec_mulVec,←mulVec_mulVec,dotProduct_mulVec,←mulVec_transpose,centering_symmetric]

lemma laplacian_ones (G : MultiGraph n m) : G.laplacian univ *ᵥ ones n=0 := by
  simp only [laplacian,sum_mulVec,vecMulVec_mulVec]
  apply Finset.sum_eq_zero
  intro e _
  rw [dotProduct_comm]
  change MulOpposite.op (∑v, ones n v*G.incidence e v) • G.incidence e=0
  rw [G.eval_incidence]
  simp [ones]

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_ConicDuality
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric conic duality. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree
open scoped Classical MatrixOrder Topology
open Filter

section Pairing
variable {n : ℕ}

lemma trace_gram_pairing (B X : Matrix (Fin n) (Fin n) ℝ) :
    (B*(Xᵀ*X)).trace=∑i, qform B (X i) := by
  rw [←mul_assoc,trace_mul_cycle]
  apply sum_congr rfl
  intro i _
  simp only [diag_apply,mul_apply,transpose_apply,qform,mulVec,dotProduct]
  simp only [sum_mul,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro k _
  ring

lemma trace_pairing_nonneg {B Z : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.PosSemidef) (hZ : Z.PosSemidef) : 0 ≤ (B*Z).trace := by
  conv_rhs => rw [←sqrt_gram hZ]
  rw [trace_gram_pairing]
  exact sum_nonneg (fun i _ => qform_nonneg hB _)

lemma test_one : Test (1 : Matrix (Fin n) (Fin n) ℝ) := by
  refine ⟨Matrix.PosSemidef.one,?_⟩
  intro u v w
  have heq (a b : Fin n) : qform (1 : Matrix (Fin n) (Fin n) ℝ) (difference a b)=
      if a=b then 0 else 2 := by
    by_cases hab : a=b
    · simp [hab,difference,qform]
    · norm_num [qform,difference,MultiGraph.point,sub_dotProduct,dotProduct_sub,hab,Ne.symm hab]
  simp only [heq]
  split_ifs <;> try norm_num
  all_goals simp_all

end Pairing
end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_CenteredDomain
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.Partitions.mem_crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Centered domain. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder Matrix.Norms.Elementwise

variable {n m : ℕ}

lemma mul_constant_of_ones {D : Matrix (Fin n) (Fin n) ℝ} (hD0 : D *ᵥ ones n=0) :
    D*constantProjection n=0 := by
  simp only [constantProjection,mul_smul_comm,mul_vecMulVec,hD0,zero_vecMulVec,smul_zero]

lemma constant_mul_of_ones {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.IsHermitian)
    (hD0 : D *ᵥ ones n=0) : constantProjection n*D=0 := by
  have hh := congrArg transpose (mul_constant_of_ones hD0)
  simpa only [transpose_mul,constantProjection_symmetric,
    (isHermitian_iff_isSymm.mp hD).eq,transpose_zero] using hh

lemma mul_centering_of_ones {D : Matrix (Fin n) (Fin n) ℝ} (hD0 : D *ᵥ ones n=0) :
    D*centering n=D := by
  rw [centering,mul_sub,mul_one,mul_constant_of_ones hD0,sub_zero]

lemma centering_mul_of_ones {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.IsHermitian)
    (hD0 : D *ᵥ ones n=0) : centering n*D=D := by
  rw [centering,sub_mul,one_mul,constant_mul_of_ones hD hD0,sub_zero]

lemma centered_eq {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.IsHermitian)
    (hD0 : D *ᵥ ones n=0) : centered D=D := by
  rw [centered,centering_mul_of_ones hD hD0,mul_centering_of_ones hD0]

lemma laplacian_mem_domain (G : MultiGraph n m) : G.laplacian univ ∈ metricDomain G := by
  refine ⟨(G.laplacian_psd univ).isHermitian,laplacian_ones G,le_rfl,?_⟩
  intro Z hZ
  have hh := trace_pairing_nonneg (G.laplacian_psd univ) hZ.1.1
  linarith only [hh]

lemma domain_psd (G : MultiGraph n m) {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X ∈ metricDomain G) : X.PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp ((Matrix.nonneg_iff_posSemidef.mpr (G.laplacian_psd univ)).trans hX.2.2.1)

lemma domain_closed (G : MultiGraph n m) : IsClosed (metricDomain G) := by
  have hc : Continuous (fun X : Matrix (Fin n) (Fin n) ℝ => X *ᵥ ones n) := by
    fun_prop
  have ht : IsClosed {X : Matrix (Fin n) (Fin n) ℝ | ∀Z, CenteredTest Z →
      (X*Z).trace ≤ (3:ℝ)*(G.laplacian univ*Z).trace} := by
    simp only [show {X : Matrix (Fin n) (Fin n) ℝ | ∀Z, CenteredTest Z →
      (X*Z).trace ≤ (3:ℝ)*(G.laplacian univ*Z).trace} =
      ⋂ Z : {Z : Matrix (Fin n) (Fin n) ℝ // CenteredTest Z},
        {X | (X*Z.val).trace ≤ 3*(G.laplacian univ*Z.val).trace} by ext; simp]
    exact isClosed_iInter fun Z => isClosed_le (trace_pairing_continuous _) continuous_const
  exact (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).inter
    ((isClosed_eq hc continuous_const).inter ((isClosed_matrixAbove _).inter ht))

lemma domain_convex (G : MultiGraph n m) : Convex ℝ (metricDomain G) := by
  intro X hX Y hY a b ha hb hab
  refine ⟨(hX.1.smul (isSelfAdjoint_iff.mpr (star_trivial a))).add (hY.1.smul (isSelfAdjoint_iff.mpr (star_trivial b))),?_,?_,?_⟩
  · simp only [add_mulVec,smul_mulVec,hX.2.1,hY.2.1,smul_zero,add_zero]
  · apply Matrix.le_iff.mpr
    have h := ((Matrix.le_iff.mp hX.2.2.1).smul ha).add ((Matrix.le_iff.mp hY.2.2.1).smul hb)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    rw [smul_sub,smul_sub]
    have hh : a • G.laplacian univ+b • G.laplacian univ=G.laplacian univ := by
      rw [←add_smul,hab,one_smul]
    nth_rw 1 [←hh]
    abel
  · intro Z hZ
    simp only [add_mul,smul_mul_assoc,trace_add,trace_smul,smul_eq_mul]
    calc
      a*(X*Z).trace+b*(Y*Z).trace ≤ a*(3*(G.laplacian univ*Z).trace)+b*(3*(G.laplacian univ*Z).trace) :=
        add_le_add (mul_le_mul_of_nonneg_left (hX.2.2.2 Z hZ) ha) (mul_le_mul_of_nonneg_left (hY.2.2.2 Z hZ) hb)
      _ = 3*(G.laplacian univ*Z).trace := by rw [←add_mul,hab,one_mul]

lemma difference_sum (u v : Fin n) : (∑i, difference u v i)=0 := by
  simp [difference,point,sum_sub_distrib]

lemma test_centered (hn : 0 < n) {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Test Z) :
    CenteredTest (centered Z) := by
  refine ⟨⟨centered_psd hZ.1,?_⟩,centered_ones hn Z⟩
  intro u v w
  simpa only [qform_centered,centering_mulVec_of_sum_zero (difference_sum _ _)] using hZ.2 u v w

lemma centered_one (hn : 0 < n) : centered (1 : Matrix (Fin n) (Fin n) ℝ)=centering n := by
  rw [centered,mul_one,mul_centering_of_ones (centering_ones hn)]

lemma centering_test (hn : 0 < n) : CenteredTest (centering n) := by
  simpa only [centered_one hn] using test_centered hn (test_one (n:=n))

lemma domain_trace_bound (G : MultiGraph n m) (hn : 0 < n) {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X ∈ metricDomain G) : X.trace ≤ 3*(G.laplacian univ).trace := by
  have hh := hX.2.2.2 _ (centering_test hn)
  simpa only [mul_centering_of_ones hX.2.1,mul_centering_of_ones (laplacian_ones G)] using hh

lemma domain_bounded (G : MultiGraph n m) (hn : 0 < n) : Bornology.IsBounded (metricDomain G) := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨3*(G.laplacian univ).trace,fun X hX => ?_⟩
  have ht := domain_trace_bound G hn hX
  have hp := domain_psd G hX
  have hC : 0 ≤ 3*(G.laplacian univ).trace := mul_nonneg (by norm_num) (G.laplacian_psd univ).trace_nonneg
  have hd (i : Fin n) : X i i ≤ 3*(G.laplacian univ).trace :=
    (single_le_sum (fun j _ => hp.diag_nonneg (i:=j)) (mem_univ i)).trans ht
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro j
  simpa only [Real.norm_eq_abs] using psd_entry_bound hp hC hd i j

lemma domain_compact (G : MultiGraph n m) (hn : 0 < n) : IsCompact (metricDomain G) :=
  Metric.isCompact_iff_isClosed_bounded.mpr ⟨domain_closed G,domain_bounded G hn⟩

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_ConcaveAlternative
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concave alternative. -/

section

namespace AlgorithmicThinTrees.ConvexAlternative
noncomputable section
open Finset
open scoped Classical
variable {E I : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [Fintype I]

theorem compact_concave_alternative (C : Set E) (hcompact : IsCompact C)
    (hne : C.Nonempty) (hconvex : Convex ℝ C) (f : I → E → ℝ)
    (hcontinuous : ∀i, ContinuousOn (f i) C)
    (hconcave : ∀i, ConcaveOn ℝ C (f i))
    (hinfeasible : ¬∃x ∈ C, ∀i, 0 ≤ f i x) :
    ∃ε : ℝ, 0 < ε ∧ ∃w : I → ℝ, (∀i, 0 ≤ w i) ∧ (∑i, w i)=1 ∧
      ∀x ∈ C, (∑i, w i*f i x) ≤ -ε := by
  let b : E → ℝ := fun x => ∑i, max 0 (-f i x)
  have hbcont : ContinuousOn b C := by
    apply continuousOn_finsetSum
    intro i _
    exact continuousOn_const.sup (hcontinuous i).neg
  have hbpos : ∀x ∈ C, 0 < b x := by
    intro x hx
    have he : ∃i, f i x < 0 := by
      by_contra hh
      apply hinfeasible
      exact ⟨x,hx,fun i => le_of_not_gt (fun hi => hh ⟨i,hi⟩)⟩
    obtain ⟨i,hi⟩ := he
    apply sum_pos' (fun _ _ => le_max_left _ _)
    exact ⟨i,mem_univ i,(neg_pos.mpr hi).trans_le (le_max_right _ _)⟩
  obtain ⟨x₀,hx₀,hmin⟩ := hcompact.exists_isMinOn hne hbcont
  let ε := b x₀/((Fintype.card I:ℝ)+1)
  have hε : 0 < ε := div_pos (hbpos x₀ hx₀) (by positivity)
  have heq : ((Fintype.card I:ℝ)+1)*ε=b x₀ := by
    dsimp [ε]
    exact mul_div_cancel₀ _ (by positivity)
  have hno : ¬∃x ∈ C, ∀i, (-f i x)-ε < 0 := by
    rintro ⟨x,hx,hh⟩
    have hbx : b x ≤ (Fintype.card I:ℝ)*ε := by
      calc
        _ ≤ ∑i : I, ε := sum_le_sum (fun i _ => max_le hε.le (by linarith [hh i]))
        _ = _ := by simp
    have hminx := (isMinOn_iff.mp hmin) x hx
    nlinarith only [hbx,hminx,heq,hε]
  have hc : ∀i, ConvexOn ℝ C (fun x => -f i x-ε) := by
    intro i
    refine ⟨hconvex,?_⟩
    intro x hx y hy a d ha hd had
    have hh := (hconcave i).2 hx hy ha hd had
    change a*f i x+d*f i y ≤ f i (a • x+d • y) at hh
    change -f i (a • x+d • y)-ε ≤ a*(-f i x-ε)+d*(-f i y-ε)
    nlinarith only [hh,congrArg (fun z : ℝ => z*ε) had]
  obtain ⟨w,hw,hws,hbound⟩ := StrongThinTree.Duality.convex_alternative C hconvex hne
    (fun i x => -f i x-ε) hc hno
  refine ⟨ε,hε,w,hw,hws,?_⟩
  intro x hx
  have hh := hbound x hx
  simp only [mul_sub,mul_neg,sum_sub_distrib,sum_neg_distrib,←sum_mul,hws,one_mul] at hh
  linarith

end
end AlgorithmicThinTrees.ConvexAlternative
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_PartitionLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partition lattice. -/

section

namespace AlgorithmicThinTrees.Partitions
noncomputable section
open Finset
open scoped Classical

variable {V E : Type*} [Fintype V]

omit [Fintype V] in
lemma constants_antitone {p q : Setoid V} (hpq : p ≤ q) : constants q ≤ constants p :=
  fun _ hx => hpq.trans hx

omit [Fintype V] in
lemma constants_sup (p q : Setoid V) : constants (p ⊔ q)=constants p ⊓ constants q := by
  ext x
  change (p ⊔ q ≤ Setoid.ker x) ↔ (p ≤ Setoid.ker x) ∧ (q ≤ Setoid.ker x)
  exact sup_le_iff

lemma constants_finrank (p : Setoid V) : Module.finrank ℝ (constants p)=partCount p := by
  rw [←(quotientConstants p).finrank_eq,Module.finrank_pi]
  rfl

theorem partCount_supermodular (p q : Setoid V) :
    partCount p+partCount q ≤ partCount (p ⊓ q)+partCount (p ⊔ q) := by
  have hi : constants p ⊔ constants q ≤ constants (p ⊓ q) :=
    sup_le (constants_antitone inf_le_left) (constants_antitone inf_le_right)
  have hr := Submodule.finrank_mono hi
  have he := Submodule.finrank_sup_add_finrank_inf_eq (constants p) (constants q)
  rw [←constants_sup,constants_finrank,constants_finrank,constants_finrank] at he
  rw [constants_finrank] at hr
  omega

theorem partCount_strictAnti : StrictAnti (partCount (V := V)) := by
  intro p q hpq
  let f : Quotient p → Quotient q := Quotient.map id hpq.le
  have hsur : Function.Surjective f := Quotient.map_surjective hpq.le Function.surjective_id
  have hninj : ¬Function.Injective f := by
    intro hinj
    have hqp : q ≤ p := by
      intro a b hab
      apply Quotient.exact
      apply hinj
      change (Quotient.mk q a)=(Quotient.mk q b)
      exact Quotient.sound hab
    exact (not_le_of_gt hpq) hqp
  exact Fintype.card_lt_of_surjective_not_injective f hsur hninj

theorem potential_uncross {p q : Setoid V} (hpq : ¬p ≤ q) (hqp : ¬q ≤ p) :
    potential p+potential q < potential (p ⊓ q)+potential (p ⊔ q) := by
  have hip : p ⊓ q < p := lt_of_le_of_ne inf_le_left (by
    intro he
    exact hpq (he ▸ inf_le_right))
  have hiq : p ⊓ q < q := lt_of_le_of_ne inf_le_right (by
    intro he
    exact hqp (he ▸ inf_le_left))
  have hps : p < p ⊔ q := lt_of_le_of_ne le_sup_left (by
    intro he
    exact hqp (he.symm ▸ le_sup_right))
  have hqs : q < p ⊔ q := lt_of_le_of_ne le_sup_right (by
    intro he
    exact hpq (he.symm ▸ le_sup_left))
  have hcp : (partCount p:ℝ) < partCount (p ⊓ q) := by exact_mod_cast partCount_strictAnti hip
  have hcq : (partCount q:ℝ) < partCount (p ⊓ q) := by exact_mod_cast partCount_strictAnti hiq
  have hdp : (partCount (p ⊔ q):ℝ) < partCount p := by exact_mod_cast partCount_strictAnti hps
  have hdq : (partCount (p ⊔ q):ℝ) < partCount q := by exact_mod_cast partCount_strictAnti hqs
  have hsum : (partCount p:ℝ)+partCount q ≤ partCount (p ⊓ q)+partCount (p ⊔ q) := by
    exact_mod_cast partCount_supermodular p q
  have hm1 := mul_pos (sub_pos.mpr hcp) (sub_pos.mpr hcq)
  have hm2 := mul_nonneg (sub_nonneg.mpr hdp.le) (sub_nonneg.mpr hdq.le)
  have hm3 := mul_nonneg (show (0:ℝ) ≤ partCount p+partCount q by positivity)
    (sub_nonneg.mpr hsum)
  dsimp [potential]
  nlinarith only [hm1,hm2,hm3]

omit [Fintype V] in
lemma crossingIndicator_nonneg (p : Setoid V) (a b : V) : 0 ≤ crossingIndicator p a b := by
  unfold crossingIndicator
  split_ifs <;> norm_num

omit [Fintype V] in
theorem crossingIndicator_submodular (p q : Setoid V) (a b : V) :
    crossingIndicator (p ⊓ q) a b+crossingIndicator (p ⊔ q) a b ≤
      crossingIndicator p a b+crossingIndicator q a b := by
  have hp : p a b → (p ⊔ q) a b := fun h => (show p ≤ p ⊔ q from le_sup_left) h
  have hq : q a b → (p ⊔ q) a b := fun h => (show q ≤ p ⊔ q from le_sup_right) h
  have hinf : (p ⊓ q) a b ↔ p a b ∧ q a b := Iff.rfl
  unfold crossingIndicator
  by_cases habp : p a b <;> by_cases habq : q a b
  · simp [hinf,habp,habq,hp habp]
  · simp [hinf,habp,habq,hp habp]
  · simp [hinf,habp,habq,hq habq]
  · simp only [hinf,habp,habq,false_and,ite_false, if_false]
    split_ifs <;> norm_num

variable [Fintype E]

omit [Fintype V] in
theorem capacity_submodular (left right : E → V) (w : E → ℝ) (hw : ∀e, 0 ≤ w e)
    (p q : Setoid V) :
    capacity left right w (p ⊓ q)+capacity left right w (p ⊔ q) ≤
      capacity left right w p+capacity left right w q := by
  simp only [capacity,←sum_add_distrib,←mul_add]
  exact sum_le_sum (fun e _ => mul_le_mul_of_nonneg_left
    (crossingIndicator_submodular p q (left e) (right e)) (hw e))

theorem slack_submodular (left right : E → V) (w : E → ℝ) (hw : ∀e, 0 ≤ w e)
    {r : ℝ} (hr : 0 ≤ r) (p q : Setoid V) :
    slack left right w r (p ⊓ q)+slack left right w r (p ⊔ q) ≤
      slack left right w r p+slack left right w r q := by
  have hc := capacity_submodular left right w hw p q
  have hrank : (partCount p:ℝ)+partCount q ≤ partCount (p ⊓ q)+partCount (p ⊔ q) := by
    exact_mod_cast partCount_supermodular p q
  have hm := mul_le_mul_of_nonneg_left hrank hr
  dsimp [slack]
  linarith

end
end AlgorithmicThinTrees.Partitions
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_PartitionGeometry
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partition geometry. -/

section

namespace AlgorithmicThinTrees.Partitions
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical

variable {V : Type*} [Fintype V]

lemma block_block (p : Setoid V) {a b v : V} (ha : a ∈ block p v) (hb : b ∈ block p v) :
    p a b := p.trans (p.symm ((mem_block _ _ _).mp ha)) ((mem_block _ _ _).mp hb)

lemma parts_top [Nonempty V] : parts (⊤ : Setoid V)={univ} := by
  have hb (v : V) : block (⊤ : Setoid V) v=univ := by ext w; simp [block]
  unfold parts
  rw [show block (⊤ : Setoid V)=(fun _ => univ) from funext hb]
  exact image_const univ_nonempty _

lemma partCount_pos [Nonempty V] (p : Setoid V) : 0 < partCount p :=
  Fintype.card_pos_iff.mpr ⟨Quotient.mk p (Classical.arbitrary V)⟩

lemma partCount_top [Nonempty V] : partCount (⊤ : Setoid V)=1 := by
  apply Fintype.card_eq_one_iff.mpr
  refine ⟨Quotient.mk ⊤ (Classical.arbitrary V),?_⟩
  intro y
  induction y using Quotient.inductionOn with
  | h y => exact Quotient.sound trivial

lemma two_le_partCount [Nonempty V] {p : Setoid V} (hp : p ≠ ⊤) : 2 ≤ partCount p := by
  have hh := partCount_strictAnti (lt_top_iff_ne_top.mpr hp)
  rw [partCount_top] at hh
  exact hh

variable {n m : ℕ}

lemma capacity_eq_sum (G : MultiGraph n m) (w : Fin m → ℝ) (p : Setoid (Fin n)) :
    capacity G.left G.right w p=∑e ∈ crossing G p, w e := by
  simp only [capacity,crossing,sum_filter,crossingIndicator]
  apply sum_congr rfl
  intro e _
  split_ifs <;> simp_all

end
end AlgorithmicThinTrees.Partitions
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Ramp
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation ramp. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder

variable {n m : ℕ}

lemma lowerCapacity_lower {κ t u y : ℝ} (ht : 0 ≤ t) (hy : 0 ≤ y) :
    κ-4*t ≤ lowerCapacity κ t u y := by
  unfold lowerCapacity
  split_ifs with hu
  · have hm : -4*t ≤ min 1 (u+t*(5*y-4)) := by
      apply le_min
      · linarith
      · nlinarith [mul_nonneg ht hy]
    linarith
  · linarith

lemma lowerCapacity_nonneg {κ t u y : ℝ} (ht : 0 ≤ t) (hy : 0 ≤ y) (hκ : 4*t ≤ κ) :
    0 ≤ lowerCapacity κ t u y := (sub_nonneg.mpr hκ).trans (lowerCapacity_lower ht hy)

lemma lowerCapacity_le {κ t u y : ℝ} : lowerCapacity κ t u y ≤ κ+1 := by
  unfold lowerCapacity
  split_ifs
  · exact add_le_add_right (min_le_left _ _) κ
  · linarith

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Domain
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation domain. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder Matrix.Norms.Elementwise

variable {n m : ℕ}

lemma admissible_nonempty (H : MultiGraph n m) (s : ℝ) (u : Fin m → ℝ) :
    (admissible H s u).Nonempty := by
  refine ⟨(H.laplacian univ,0),laplacian_mem_domain H,fun e => ?_,?_⟩
  · exact ⟨le_rfl,by norm_num⟩
  · intro e _
    simp only [Pi.zero_apply,mul_zero,zero_smul]
    exact Matrix.nonneg_iff_posSemidef.mpr (H.laplacian_psd univ)

lemma admissible_closed (H : MultiGraph n m) (s : ℝ) (u : Fin m → ℝ) :
    IsClosed (admissible H s u) := by
  have hY : IsClosed {x : ResponseSpace n m | x.1 ∈ metricDomain H} :=
    (domain_closed H).preimage continuous_fst
  have hy : IsClosed {x : ResponseSpace n m | ∀e, 0 ≤ x.2 e ∧ x.2 e ≤ 1} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro e
    exact (isClosed_le continuous_const ((continuous_apply e).comp continuous_snd)).inter
      (isClosed_le ((continuous_apply e).comp continuous_snd) continuous_const)
  have hl : IsClosed {x : ResponseSpace n m | ∀e, 0 < u e →
      (6*s*x.2 e) • vecMulVec (H.incidence e) (H.incidence e) ≤ x.1} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro e
    apply isClosed_iInter
    intro _
    have hc : Continuous (fun x : ResponseSpace n m =>
        x.1-(6*s*x.2 e) • vecMulVec (H.incidence e) (H.incidence e)) := by fun_prop
    convert (isClosed_matrixAbove (0 : Matrix (Fin n) (Fin n) ℝ)).preimage hc using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [Set.mem_preimage,Set.mem_ofPred_eq,sub_nonneg]
  exact hY.inter (hy.inter hl)

lemma admissible_compact (H : MultiGraph n m) (hn : 0 < n) (s : ℝ) (u : Fin m → ℝ) :
    IsCompact (admissible H s u) := by
  have hb : IsCompact {y : Fin m → ℝ | ∀e, y e ∈ Set.Icc (0:ℝ) 1} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  apply ((domain_compact H hn).prod hb).of_isClosed_subset (admissible_closed H s u)
  intro x hx
  exact ⟨hx.1,hx.2.1⟩

lemma admissible_convex (H : MultiGraph n m) (s : ℝ) (u : Fin m → ℝ) :
    Convex ℝ (admissible H s u) := by
  intro x hx z hz a b ha hb hab
  refine ⟨domain_convex H hx.1 hz.1 ha hb hab,?_,?_⟩
  · intro e
    change 0 ≤ a*x.2 e+b*z.2 e ∧ a*x.2 e+b*z.2 e ≤ 1
    refine ⟨add_nonneg (mul_nonneg ha (hx.2.1 e).1) (mul_nonneg hb (hz.2.1 e).1),?_⟩
    have h1 := mul_le_mul_of_nonneg_left (hx.2.1 e).2 ha
    have h2 := mul_le_mul_of_nonneg_left (hz.2.1 e).2 hb
    nlinarith only [h1,h2,hab]
  · intro e he
    apply Matrix.le_iff.mpr
    have h1 := (Matrix.le_iff.mp (hx.2.2 e he)).smul ha
    have h2 := (Matrix.le_iff.mp (hz.2.2 e he)).smul hb
    convert h1.add h2 using 1
    all_goals try with_reducible_and_instances rfl
    change a • x.1+b • z.1-(6*s*(a*x.2 e+b*z.2 e)) •
      vecMulVec (H.incidence e) (H.incidence e)=_
    simp only [smul_sub,smul_smul]
    module

lemma lowerCapacity_continuous (κ t u : ℝ) : Continuous (lowerCapacity κ t u) := by
  unfold lowerCapacity
  split_ifs
  · fun_prop
  · exact continuous_const

lemma lowerCapacity_concave (κ t u : ℝ) : ConcaveOn ℝ Set.univ (lowerCapacity κ t u) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  change a*lowerCapacity κ t u x+b*lowerCapacity κ t u y ≤
    lowerCapacity κ t u (a*x+b*y)
  unfold lowerCapacity
  split_ifs with hu
  · have h1 := mul_le_mul_of_nonneg_left (min_le_left (1:ℝ) (u+t*(5*x-4))) ha
    have h2 := mul_le_mul_of_nonneg_left (min_le_left (1:ℝ) (u+t*(5*y-4))) hb
    have h3 := mul_le_mul_of_nonneg_left (min_le_right (1:ℝ) (u+t*(5*x-4))) ha
    have h4 := mul_le_mul_of_nonneg_left (min_le_right (1:ℝ) (u+t*(5*y-4))) hb
    have hc : a*κ+b*κ=κ := by rw [←add_mul,hab,one_mul]
    have hlin : a*(u+t*(5*x-4))+b*(u+t*(5*y-4))=u+t*(5*(a*x+b*y)-4) := by
      calc
        _ = (a+b)*(u-4*t)+5*t*(a*x+b*y) := by ring
        _ = _ := by rw [hab]; ring
    conv_rhs => rw [add_min]
    apply le_min <;> nlinarith only [h1,h2,h3,h4,hc,hlin,hab]
  · rw [←add_mul,hab,one_mul]

lemma responseSlack_continuous (H : MultiGraph n m) (κ t Q : ℝ) (u : Fin m → ℝ)
    (p : Setoid (Fin n)) : Continuous (responseSlack H κ t Q u p) := by
  unfold responseSlack Partitions.slack Partitions.capacity
  apply Continuous.sub _ continuous_const
  apply continuous_finsetSum
  intro e _
  exact ((lowerCapacity_continuous κ t (u e)).comp
    ((continuous_apply e).comp continuous_snd)).mul_const _

lemma responseSlack_concave (H : MultiGraph n m) (κ t Q s : ℝ) (u : Fin m → ℝ)
    (p : Setoid (Fin n)) : ConcaveOn ℝ (admissible H s u) (responseSlack H κ t Q u p) := by
  refine ⟨admissible_convex H s u,?_⟩
  intro x hx z hz a b ha hb hab
  have hsum := sum_le_sum (s:=Partitions.crossing H p) (fun e (_ : e ∈ Partitions.crossing H p) =>
    (lowerCapacity_concave κ t (u e)).2 (Set.mem_univ (x.2 e)) (Set.mem_univ (z.2 e)) ha hb hab)
  simp only [smul_eq_mul,←mul_sum,sum_add_distrib] at hsum
  change a*responseSlack H κ t Q u p x+b*responseSlack H κ t Q u p z ≤
    responseSlack H κ t Q u p (a • x+b • z)
  unfold responseSlack Partitions.slack
  rw [Partitions.capacity_eq_sum,Partitions.capacity_eq_sum,Partitions.capacity_eq_sum]
  have hc : a*(Q*((Partitions.partCount p:ℝ)-1))+b*(Q*((Partitions.partCount p:ℝ)-1))=
      Q*((Partitions.partCount p:ℝ)-1) := by rw [←add_mul,hab,one_mul]
  change a*((∑e ∈ Partitions.crossing H p, lowerCapacity κ t (u e) (x.2 e))-
        Q*((Partitions.partCount p:ℝ)-1))+
      b*((∑e ∈ Partitions.crossing H p, lowerCapacity κ t (u e) (z.2 e))-
        Q*((Partitions.partCount p:ℝ)-1)) ≤
      (∑e ∈ Partitions.crossing H p, lowerCapacity κ t (u e) (a*x.2 e+b*z.2 e))-
        Q*((Partitions.partCount p:ℝ)-1)
  nlinarith only [hsum,hc]

lemma responseSlack_submodular (H : MultiGraph n m) {κ t Q s : ℝ} (u : Fin m → ℝ)
    (ht : 0 ≤ t) (hκ : 4*t ≤ κ) (hQ : 0 ≤ Q) {x : ResponseSpace n m}
    (hx : x ∈ admissible H s u) (p q : Setoid (Fin n)) :
    responseSlack H κ t Q u (p ⊓ q) x+responseSlack H κ t Q u (p ⊔ q) x ≤
      responseSlack H κ t Q u p x+responseSlack H κ t Q u q x :=
  Partitions.slack_submodular H.left H.right _
    (fun e => lowerCapacity_nonneg ht (hx.2.1 e).1 hκ) hQ p q

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_ConeRepresentation
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_mat _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_mul _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.step_mul _root_.OAI.AlgorithmicThinTrees.Partitions.mem_crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric cone representation. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder Matrix.Norms.Elementwise Topology
open Filter

section Representation
variable {n : ℕ} {J : Type*} [Fintype J]

lemma psd_mem_coneImage (W : J → Matrix (Fin n) (Fin n) ℝ)
    {P : Matrix (Fin n) (Fin n) ℝ} (hP : P.PosSemidef) : P ∈ coneImage W := by
  exact ⟨P,fun _ => 0,hP,fun _ => le_refl _,by simp⟩

lemma generator_mem_coneImage (W : J → Matrix (Fin n) (Fin n) ℝ) (j : J) :
    W j ∈ coneImage W := by
  refine ⟨0,Pi.single j 1,PosSemidef.zero,?_,?_⟩
  · intro i
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  · simp [Pi.single_apply]

end Representation
section TraceDual
variable {n : ℕ}

lemma linearTraceMatrix_pairing (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) : (X*linearTraceMatrix f).trace=f X := by
  have hf : f X = ∑i, ∑j, X i j*f (Matrix.single i j 1) := by
    nth_rw 1 [matrix_eq_sum_single X]
    simp only [map_sum]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    rw [show Matrix.single i j (X i j)=(X i j) • Matrix.single i j (1 : ℝ) by
      simp only [smul_single,smul_eq_mul,mul_one]]
    simp only [map_smul,smul_eq_mul]
  simpa only [Matrix.trace,diag_apply,mul_apply,linearTraceMatrix] using hf.symm

lemma trace_pairing_transpose_right {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.IsHermitian) (Z : Matrix (Fin n) (Fin n) ℝ) :
    (X*Zᵀ).trace=(X*Z).trace := by
  rw [←trace_transpose (X*Zᵀ),transpose_mul,transpose_transpose,
    (isHermitian_iff_isSymm.mp hX).eq,trace_mul_comm]

lemma symmetricTraceMatrix_hermitian (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ) :
    (symmetricTraceMatrix f).IsHermitian := by
  apply isHermitian_iff_isSymm.mpr
  simp only [IsSymm,symmetricTraceMatrix,transpose_smul,transpose_add,transpose_transpose]
  rw [add_comm]

lemma symmetricTraceMatrix_pairing (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.IsHermitian) :
    (X*symmetricTraceMatrix f).trace=f X := by
  rw [symmetricTraceMatrix,mul_smul_comm,mul_add,trace_smul,trace_add,
    trace_pairing_transpose_right hX,linearTraceMatrix_pairing]
  simp only [smul_eq_mul]
  ring

lemma symmetricTraceMatrix_psd (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ)
    (hf : ∀ P : Matrix (Fin n) (Fin n) ℝ, P.PosSemidef → 0 ≤ f P) :
    (symmetricTraceMatrix f).PosSemidef := by
  apply PosSemidef.of_dotProduct_mulVec_nonneg (symmetricTraceMatrix_hermitian f)
  intro x
  simpa only [star_trivial,←ShortcutDual.trace_outer_mul,
    symmetricTraceMatrix_pairing f (ShortcutDual.outer_posSemidef x).isHermitian]
    using hf (vecMulVec x x) (ShortcutDual.outer_posSemidef x)

lemma difference_norm_sq {u v : Fin n} (huv : u ≠ v) :
    difference u v ⬝ᵥ difference u v=2 := by
  norm_num [difference,point,sub_dotProduct,dotProduct_sub,huv,huv.symm]

lemma triangleGenerator_trace (ijk : DistinctTriple n) : (triangleGenerator ijk).trace=2 := by
  simp only [triangleGenerator,triangleMatrix,trace_sub,trace_add,trace_vecMulVec,
    difference_norm_sq ijk.property.1,difference_norm_sq ijk.property.2.1,
    difference_norm_sq ijk.property.2.2]
  norm_num

lemma triangleMatrix_ones (u v w : Fin n) : triangleMatrix u v w *ᵥ ones n=0 := by
  have h (a b : Fin n) : vecMulVec (difference a b) (difference a b) *ᵥ ones n=0 := by
    rw [vecMulVec_mulVec,dotProduct_comm,ones_dot,difference_sum,MulOpposite.op_zero,zero_smul]
  simp only [triangleMatrix,sub_mulVec,add_mulVec,h,zero_add,sub_zero]

lemma triangleMatrix_pairing (u v w : Fin n) (Z : Matrix (Fin n) (Fin n) ℝ) :
    (triangleMatrix u v w*Z).trace=
      qform Z (difference u v)+qform Z (difference v w)-qform Z (difference u w) := by
  simp only [triangleMatrix,sub_mul,add_mul,trace_add,trace_sub,ShortcutDual.trace_outer_mul,qform]

lemma test_iff_generators (Z : Matrix (Fin n) (Fin n) ℝ) :
    Test Z ↔ Z.PosSemidef ∧ ∀ijk : DistinctTriple n, 0 ≤ (triangleGenerator ijk*Z).trace := by
  refine ⟨fun hZ => ⟨hZ.1,fun ijk => ?_⟩,fun hZ => ⟨hZ.1,fun u v w => ?_⟩⟩
  · simpa only [triangleGenerator,triangleMatrix_pairing,sub_nonneg] using hZ.2 _ _ _
  · by_cases huv : u=v
    · subst v
      simp [difference,qform]
    by_cases hvw : v=w
    · subst w
      simp [difference,qform]
    by_cases huw : u=w
    · subst w
      simpa only [difference,sub_self,mulVec_zero,dotProduct_zero,qform]
        using add_nonneg (qform_nonneg hZ.1 (difference u v)) (qform_nonneg hZ.1 (difference v u))
    have hh := hZ.2 ⟨(u,v,w),huv,hvw,huw⟩
    simpa only [triangleGenerator,triangleMatrix_pairing,sub_nonneg] using hh

theorem metric_dual_representation {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) :
    (∀Z, Test Z → 0 ≤ (A*Z).trace) ↔ A ∈ coneImage (triangleGenerator (n:=n)) := by
  constructor
  · intro hdual
    by_contra hn
    let : LocallyConvexSpace ℝ (Matrix (Fin n) (Fin n) ℝ) :=
      inferInstanceAs (LocallyConvexSpace ℝ (Fin n → Fin n → ℝ))
    obtain ⟨f,hf,hfA⟩ := (representedCone triangleGenerator triangleGenerator_trace).hyperplane_separation_point hn
    have hfP : ∀P : Matrix (Fin n) (Fin n) ℝ, P.PosSemidef → 0 ≤ f P :=
      fun P hP => hf P (psd_mem_coneImage triangleGenerator hP)
    let Z := symmetricTraceMatrix f.toLinearMap
    have hZ : Test Z := by
      apply (test_iff_generators Z).mpr
      refine ⟨symmetricTraceMatrix_psd f.toLinearMap hfP,fun ijk => ?_⟩
      change 0 ≤ (triangleGenerator ijk*symmetricTraceMatrix f.toLinearMap).trace
      have hi : (triangleGenerator ijk).IsHermitian := triangleMatrix_hermitian _ _ _
      rw [symmetricTraceMatrix_pairing f.toLinearMap hi]
      exact hf _ (generator_mem_coneImage triangleGenerator ijk)
    have hz := hdual Z hZ
    rw [symmetricTraceMatrix_pairing f.toLinearMap hA] at hz
    exact (not_lt_of_ge hz) hfA
  · rintro ⟨P,lam,hP,hlam,rfl⟩ Z hZ
    simp only [add_mul,sum_mul,smul_mul_assoc,trace_add,trace_sum,trace_smul,smul_eq_mul]
    exact add_nonneg (trace_pairing_nonneg hP hZ.1)
      (sum_nonneg fun ijk _ => mul_nonneg (hlam ijk) (((test_iff_generators Z).mp hZ).2 ijk))

lemma trace_centered_right {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hA0 : A *ᵥ ones n=0) (Z : Matrix (Fin n) (Fin n) ℝ) :
    (A*centered Z).trace=(A*Z).trace := by
  calc
    (A*centered Z).trace=((A*centering n)*Z*centering n).trace := by
      simp only [centered,mul_assoc]
    _ = (A*Z*centering n).trace := by rw [mul_centering_of_ones hA0]
    _ = (centering n*(A*Z)).trace := trace_mul_comm _ _
    _ = (A*Z).trace := by rw [←mul_assoc,centering_mul_of_ones hA hA0]

theorem centered_metric_dual_representation (hn : 0 < n)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (hA0 : A *ᵥ ones n=0) :
    (∀Z, CenteredTest Z → 0 ≤ (A*Z).trace) ↔
      ∃P : Matrix (Fin n) (Fin n) ℝ, ∃lam : DistinctTriple n → ℝ,
        P.PosSemidef ∧ P *ᵥ ones n=0 ∧ (∀ijk, 0 ≤ lam ijk) ∧
          A=P+∑ijk, lam ijk • triangleGenerator ijk := by
  constructor
  · intro hdual
    have hd : ∀Z, Test Z → 0 ≤ (A*Z).trace := fun Z hZ => by
      have h := hdual _ (test_centered hn hZ)
      rwa [trace_centered_right hA hA0] at h
    obtain ⟨P,lam,hP,hlam,he⟩ := (metric_dual_representation hA).mp hd
    refine ⟨P,lam,hP,?_,hlam,he⟩
    rw [he,add_mulVec] at hA0
    simpa only [sum_mulVec,smul_mulVec,triangleGenerator,triangleMatrix_ones,
      smul_zero,sum_const_zero,add_zero] using hA0
  · rintro ⟨P,lam,hP,_,hlam,he⟩ Z hZ
    exact (metric_dual_representation hA).mpr ⟨P,lam,hP,hlam,he⟩ Z hZ.1

theorem metricDomain_iff_lmi {m : ℕ} (G : MultiGraph n m) (hn : 0 < n)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.IsHermitian) (hX0 : X *ᵥ ones n=0) :
    X ∈ metricDomain G ↔ G.laplacian univ ≤ X ∧
      ∃lam : DistinctTriple n → ℝ, (∀ijk, 0 ≤ lam ijk) ∧
        ((3:ℝ) • G.laplacian univ-X-∑ijk, lam ijk • triangleGenerator ijk).PosSemidef := by
  have hA : ((3:ℝ) • G.laplacian univ-X).IsHermitian :=
    ((G.laplacian_psd univ).smul (by norm_num : (0:ℝ) ≤ 3)).isHermitian.sub hX
  have hA0 : ((3:ℝ) • G.laplacian univ-X) *ᵥ ones n=0 := by
    simp only [sub_mulVec,smul_mulVec,laplacian_ones,hX0,smul_zero,sub_self]
  constructor
  · intro h
    refine ⟨h.2.2.1,?_⟩
    obtain ⟨P,lam,hP,_,hlam,he⟩ := (centered_metric_dual_representation hn hA hA0).mp
      (fun Z hZ => by
        simpa only [sub_mul,smul_mul_assoc,trace_sub,trace_smul,smul_eq_mul,sub_nonneg]
          using h.2.2.2 Z hZ)
    refine ⟨lam,hlam,?_⟩
    rwa [he,add_sub_cancel_right]
  · rintro ⟨hLX,lam,hlam,hP⟩
    refine ⟨hX,hX0,hLX,fun Z hZ => ?_⟩
    have h := (metric_dual_representation hA).mpr
      ⟨_,lam,hP,hlam,by abel⟩ Z hZ.1
    simpa only [sub_mul,smul_mul_assoc,trace_sub,trace_smul,smul_eq_mul,sub_nonneg] using h

end TraceDual

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Encoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation encoding. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped Classical MatrixOrder Matrix.Norms.Elementwise

variable {n m : ℕ}

lemma responseMatrix_fixed {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hA0 : A *ᵥ ones n=0) : responseMatrix A=A := by
  rw [responseMatrix,(isHermitian_iff_isSymm.mp hA).eq,
    show (1/2 : ℝ) • (A+A)=A by module,centered_eq hA hA0]

lemma response_to_stepFeasible (H : MultiGraph n m) (hn : 0 < n)
    {s κ t q : ℝ} {u : Fin m → ℝ} (ht : 0 ≤ t) (hκt : 4*t ≤ κ)
    {w : ResponseSpace n m} (hw : w ∈ admissible H s u)
    (hp : ∀p, 0 ≤ responseSlack H κ t q u p w) :
    ∃x ∈ stepFeasible H s κ t q u, x.matrix=w.1 ∧ x.y=w.2 := by
  obtain ⟨_,lam,hlam,hP⟩ := (metricDomain_iff_lmi H hn hw.1.1 hw.1.2.1).mp hw.1
  let z : Fin m → ℝ := fun e => lowerCapacity κ t (u e) (w.2 e)
  let x : StepFree n m := (w.1,lam,w.2,z)
  have hmat : x.matrix=w.1 := responseMatrix_fixed hw.1.1 hw.1.2.1
  have hcap : x.capacities κ u=z := by
    ext e
    simp only [StepFree.capacities,StepFree.z,x]
    split_ifs with he
    · rfl
    · simp only [z,lowerCapacity,ite_eq_right he]
  refine ⟨x,⟨?_,?_⟩,hmat,rfl⟩
  · refine ⟨?_,?_,hlam,hw.2.1,?_,?_⟩
    · simpa only [StepFree.lowerPencil,hmat] using Matrix.le_iff.mp hw.1.2.2.1
    · simpa only [StepFree.upperPencil,hmat,StepFree.multiplier,x] using hP
    · intro e
      exact ⟨lowerCapacity_nonneg ht (hw.2.1 e).1 hκt,lowerCapacity_le⟩
    · intro e he
      refine ⟨?_,?_⟩
      · simpa only [StepFree.edgePencil,hmat,StepFree.y,x] using Matrix.le_iff.mp (hw.2.2 e he)
      · change lowerCapacity κ t (u e) (w.2 e) ≤ _
        rw [lowerCapacity,ite_eq_left he]
        change κ+min 1 (u e+t*(5*w.2 e-4)) ≤ κ+u e+t*(5*w.2 e-4)
        linarith only [min_le_right (1 : ℝ) (u e+t*(5*w.2 e-4))]
  · intro p
    rw [hcap]
    exact hp p

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Restriction
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Finset
namespace StrongThinTree.MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)

lemma embedding_mem (F : Finset (Fin m)) (e : Fin F.card) : edgeEmbedding F e ∈ F :=
  (F.equivFin.symm e).property
lemma embedding_surj (F : Finset (Fin m)) {e : Fin m} (he : e ∈ F) :
    ∃i : Fin F.card, edgeEmbedding F i=e := by
  refine ⟨F.equivFin ⟨e,he⟩,?_⟩
  change (F.equivFin.symm (F.equivFin ⟨e,he⟩)).val=e
  simp
lemma restrict_cut (F : Finset (Fin m)) (T : Finset (Fin F.card)) (S : Finset (Fin n)) :
    liftEdges F ((G.restrict F).cut T S)=G.cut (liftEdges F T) S := by
  ext e
  simp only [liftEdges,cut,mem_map,mem_filter]
  constructor
  · rintro ⟨i,⟨hi,hc⟩,rfl⟩
    exact ⟨⟨i,hi,rfl⟩,hc⟩
  · rintro ⟨⟨i,hi,rfl⟩,hc⟩
    exact ⟨i,⟨hi,hc⟩,rfl⟩
lemma restrict_cut_card (F : Finset (Fin m)) (T : Finset (Fin F.card)) (S : Finset (Fin n)) :
    ((G.restrict F).cut T S).card=(G.cut (liftEdges F T) S).card := by
  rw [←G.restrict_cut]
  exact (card_map _).symm
end StrongThinTree.MultiGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_PartitionLocalConnectivity
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partition local connectivity. -/

section

namespace AlgorithmicThinTrees.Partitions
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical

variable {V : Type*} [Fintype V]

omit [Fintype V] in
lemma split_iff (p : Setoid V) (S : Finset V) (a b : V) :
    split p S a b ↔ p a b ∧ (a ∈ S ↔ b ∈ S) := by
  change (p a b ∧ (a ∈ S)=(b ∈ S)) ↔ _
  simp only [eq_iff_iff]

lemma split_strict {p : Setoid V} {v : V} {S : Finset V}
    (hne : S.Nonempty) (hS : S ⊂ block p v) : split p S < p := by
  apply lt_of_le_of_ne inf_le_left
  intro he
  obtain ⟨a,ha⟩ := hne
  have hbex : ∃b ∈ block p v, b ∉ S := by
    by_contra h
    push Not at h
    exact hS.not_ge h
  obtain ⟨b,hb,hbn⟩ := hbex
  have hab : p a b := block_block p (hS.subset ha) hb
  have hsplit : split p S a b := Eq.mpr (congrArg (fun q : Setoid V => q a b) he) hab
  exact hbn (((split_iff p S a b).mp hsplit).2.mp ha)

variable {n m : ℕ}

lemma crossing_split (G : MultiGraph n m) (p : Setoid (Fin n)) (v : Fin n)
    {S : Finset (Fin n)} (hS : S ⊆ block p v) :
    crossing G (split p S)=crossing G p ∪ G.cut (G.inducedEdges (block p v)) S := by
  ext e
  simp only [mem_crossing,split_iff,mem_union,MultiGraph.cut,mem_filter,mem_inducedEdges]
  have hl : G.left e ∈ S → G.left e ∈ block p v := fun h => hS h
  have hr : G.right e ∈ S → G.right e ∈ block p v := fun h => hS h
  have hlr : p (G.left e) (G.right e) → G.left e ∈ block p v → G.right e ∈ block p v := by
    intro he hleft
    exact (mem_block _ _ _).mpr (p.trans ((mem_block _ _ _).mp hleft) he)
  have hrl : p (G.left e) (G.right e) → G.right e ∈ block p v → G.left e ∈ block p v := by
    intro he hright
    exact (mem_block _ _ _).mpr (p.trans ((mem_block _ _ _).mp hright) (p.symm he))
  by_cases hp : p (G.left e) (G.right e) <;>
    by_cases hls : G.left e ∈ S <;> by_cases hrs : G.right e ∈ S <;> simp_all

lemma crossing_split_disjoint (G : MultiGraph n m) (p : Setoid (Fin n)) (v : Fin n)
    (S : Finset (Fin n)) :
    Disjoint (crossing G p) (G.cut (G.inducedEdges (block p v)) S) := by
  apply disjoint_left.mpr
  intro e hp hi
  have he := (mem_inducedEdges _ _ _).mp (mem_filter.mp hi).1
  exact (mem_crossing G p e).mp hp (block_block p he.1 he.2)

lemma capacity_split (G : MultiGraph n m) (w : Fin m → ℝ) (p : Setoid (Fin n)) (v : Fin n)
    {S : Finset (Fin n)} (hS : S ⊆ block p v) :
    capacity G.left G.right w (split p S)=capacity G.left G.right w p+
      ∑e ∈ G.cut (G.inducedEdges (block p v)) S, w e := by
  rw [capacity_eq_sum,capacity_eq_sum,crossing_split G p v hS,
    sum_union (crossing_split_disjoint G p v S)]

lemma split_capacity_lower (G : MultiGraph n m) (w : Fin m → ℝ) {Q : ℝ} (hQ : 0 ≤ Q)
    (hinv : ∀p, 0 ≤ slack G.left G.right w Q p)
    {p : Setoid (Fin n)} (hp : slack G.left G.right w Q p ≤ 1) (v : Fin n)
    {S : Finset (Fin n)} (hne : S.Nonempty) (hS : S ⊂ block p v) :
    Q-1 ≤ ∑e ∈ G.cut (G.inducedEdges (block p v)) S, w e := by
  have hc : partCount p+1 ≤ partCount (split p S) :=
    partCount_strictAnti (split_strict hne hS)
  have hcR : (partCount p:ℝ)+1 ≤ partCount (split p S) := by exact_mod_cast hc
  have hi := hinv (split p S)
  dsimp only [slack] at hi hp
  rw [capacity_split G w p v hS.subset] at hi
  have hh := mul_le_mul_of_nonneg_left hcR hQ
  nlinarith only [hi,hp,hh]

lemma capacity_active_upper (u : Fin m → ℝ) (_hu0 : ∀e, 0 ≤ u e) (hu1 : ∀e, u e ≤ 1)
    {κ : ℝ} (hκ : 0 ≤ κ) (F : Finset (Fin m)) :
    (∑e ∈ F, (u e+κ)) ≤ ((F ∩ active u).card:ℝ)+κ*m := by
  have hpoint (e : Fin m) : u e ≤ if e ∈ active u then (1:ℝ) else 0 := by
    split_ifs with he
    · exact hu1 e
    · have he' : ¬0 < u e := by simpa using he
      exact le_of_not_gt he'
  have hsum := sum_le_sum (fun e (_ : e ∈ F) => hpoint e)
  have he : (∑e ∈ F, if e ∈ active u then (1:ℝ) else 0)=((F ∩ active u).card:ℝ) := by
    rw [←sum_filter]
    simp only [sum_const,nsmul_eq_mul,mul_one]
    congr 1
  rw [he] at hsum
  have hcard : (F.card:ℝ) ≤ m := by
    exact_mod_cast (show F.card ≤ m by simpa only [Fintype.card_fin] using card_le_univ F)
  have hm := mul_le_mul_of_nonneg_left hcard hκ
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul]
  nlinarith only [hsum,hm]

lemma restrict_induced (G : MultiGraph n m) (F : Finset (Fin m)) (A : Finset (Fin n)) :
    liftEdges F ((G.restrict F).inducedEdges A)=G.inducedEdges A ∩ F := by
  ext e
  simp only [liftEdges,mem_map,mem_inter,mem_inducedEdges]
  constructor
  · rintro ⟨i,hi,rfl⟩
    exact ⟨hi,embedding_mem F i⟩
  · rintro ⟨hi,he⟩
    obtain ⟨i,rfl⟩ := embedding_surj F he
    exact ⟨i,hi,rfl⟩

lemma restrict_internal_cut_card (G : MultiGraph n m) (F : Finset (Fin m))
    (A S : Finset (Fin n)) :
    ((G.restrict F).cut ((G.restrict F).inducedEdges A) S).card=
      (G.cut (G.inducedEdges A) S ∩ F).card := by
  rw [G.restrict_cut_card,restrict_induced]
  congr 1
  ext e
  simp only [MultiGraph.cut,mem_filter,mem_inter]
  tauto

theorem near_tight_locally_connected (G : MultiGraph n m) (u : Fin m → ℝ)
    (hu0 : ∀e, 0 ≤ u e) (hu1 : ∀e, u e ≤ 1)
    {κ Q h : ℝ} (hκ : 0 ≤ κ) (hκm : κ*m < 1) (hQ : 0 ≤ Q) (hh : h ≤ Q-2)
    (hinv : ∀p, 0 ≤ slack G.left G.right (fun e => u e+κ) Q p)
    {p : Setoid (Fin n)} (hp : slack G.left G.right (fun e => u e+κ) Q p ≤ 1)
    {A : Finset (Fin n)} (hA : A ∈ parts p) :
    (G.restrict (active u)).EdgeConnectedReal A h := by
  obtain ⟨v,rfl⟩ := (mem_parts p A).mp hA
  intro S hne hS
  have hb := split_capacity_lower G (fun e => u e+κ) hQ hinv hp v hne hS
  have hu := capacity_active_upper u hu0 hu1 hκ (G.cut (G.inducedEdges (block p v)) S)
  rw [restrict_internal_cut_card]
  linarith only [hb,hu,hκm,hh]

end
end AlgorithmicThinTrees.Partitions
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Gains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation gains. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Finset
open scoped Classical

variable {m : ℕ}

lemma booleanResponse_bounds (good : Fin m → Prop) (e : Fin m) :
    0 ≤ booleanResponse good e ∧ booleanResponse good e ≤ 1 := by
  unfold booleanResponse
  split_ifs <;> norm_num

lemma good_capacity_nondecreasing {κ t u : ℝ} (ht : 0 ≤ t) (hu : u ≤ 1) (hu0 : 0 ≤ u) :
    u+κ ≤ lowerCapacity κ t u 1 := by
  by_cases he : 0 < u
  · simp only [lowerCapacity,ite_eq_left he]
    have hh : u ≤ min 1 (u+t*(5*(1:ℝ)-4)) := le_min hu (by linarith)
    linarith only [hh]
  · have hz : u=0 := le_antisymm (le_of_not_gt he) hu0
    simp [hz,lowerCapacity]

lemma good_capacity_unsaturated {κ t u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1/2) (ht : t ≤ 1/2) :
    lowerCapacity κ t u 1=u+κ+t := by
  rw [lowerCapacity,ite_eq_left hu,min_eq_right (by linarith : u+t*(5*(1:ℝ)-4) ≤ 1)]
  ring

lemma bad_capacity_loss {κ t u : ℝ} (ht : 0 ≤ t) (hu : 0 < u) (hu1 : u ≤ 1) :
    lowerCapacity κ t u 0=u+κ-4*t := by
  rw [lowerCapacity,ite_eq_left hu,min_eq_right (by linarith : u+t*(5*(0:ℝ)-4) ≤ 1)]
  ring

lemma inactive_capacity {κ t u y : ℝ} (hu : 0 ≤ u) (ha : ¬0 < u) :
    lowerCapacity κ t u y=u+κ := by
  have hz : u=0 := le_antisymm (le_of_not_gt ha) hu
  simp [lowerCapacity,hz]

lemma capacity_change_active (F : Finset (Fin m)) (u : Fin m → ℝ)
    (hu : ∀e, 0 ≤ u e) (κ t : ℝ) (y : Fin m → ℝ) :
    (∑e ∈ F, lowerCapacity κ t (u e) (y e))-(∑e ∈ F, (u e+κ)) =
      ∑e ∈ F ∩ Partitions.active u, (lowerCapacity κ t (u e) (y e)-(u e+κ)) := by
  rw [←sum_sub_distrib]
  symm
  apply sum_subset inter_subset_left
  intro e _ he
  have hne : ¬0 < u e := by
    intro hg
    exact he (mem_inter.mpr ⟨by assumption,(Partitions.mem_active u e).mpr hg⟩)
  rw [inactive_capacity (hu e) hne,sub_self]

lemma capacity_change_loss (F : Finset (Fin m)) (u : Fin m → ℝ)
    (hu0 : ∀e, 0 ≤ u e) (hu1 : ∀e, u e ≤ 1) (good : Fin m → Prop)
    {κ t : ℝ} (ht : 0 ≤ t) :
    -4*t*(((F ∩ Partitions.active u).filter (fun e => ¬good e)).card:ℝ) ≤
      (∑e ∈ F, lowerCapacity κ t (u e) (booleanResponse good e))-(∑e ∈ F, (u e+κ)) := by
  rw [capacity_change_active F u hu0]
  have hb (e : Fin m) (he : e ∈ F ∩ Partitions.active u) :
      (if ¬good e then -4*t else 0) ≤
        lowerCapacity κ t (u e) (booleanResponse good e)-(u e+κ) := by
    have ha : 0 < u e := (Partitions.mem_active u e).mp (mem_inter.mp he).2
    by_cases hg : good e
    · simp only [booleanResponse,hg,not_true_eq_false,ite_false, if_false,ite_true, if_true]
      linarith only [good_capacity_nondecreasing (κ:=κ) ht (hu1 e) (hu0 e)]
    · simp only [booleanResponse,hg,not_false_eq_true,ite_true, if_true,ite_false, if_false,
        bad_capacity_loss ht ha (hu1 e)]
      ring_nf
      exact le_rfl
  have hs := sum_le_sum hb
  rw [←sum_filter] at hs
  simpa only [sum_const,nsmul_eq_mul,mul_comm] using hs

lemma capacity_change_gain (F : Finset (Fin m)) (u : Fin m → ℝ)
    (hu0 : ∀e, 0 ≤ u e) (hu1 : ∀e, u e ≤ 1) (good : Fin m → Prop)
    {κ t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1/2) :
    t*((F ∩ Partitions.active u).card-
        (((F ∩ Partitions.active u).filter (fun e => 1/2<u e)).card:ℝ)-
        5*(((F ∩ Partitions.active u).filter (fun e => ¬good e)).card:ℝ)) ≤
      (∑e ∈ F, lowerCapacity κ t (u e) (booleanResponse good e))-(∑e ∈ F, (u e+κ)) := by
  rw [capacity_change_active F u hu0]
  have hb (e : Fin m) (he : e ∈ F ∩ Partitions.active u) :
      t-(if 1/2<u e then t else 0)-(if ¬good e then 5*t else 0) ≤
        lowerCapacity κ t (u e) (booleanResponse good e)-(u e+κ) := by
    have ha : 0 < u e := (Partitions.mem_active u e).mp (mem_inter.mp he).2
    by_cases hg : good e
    · simp only [booleanResponse,hg,not_true_eq_false,ite_false, if_false,ite_true, if_true,sub_zero]
      by_cases hl : 1/2<u e
      · rw [ite_eq_left hl,sub_self]
        linarith only [good_capacity_nondecreasing (κ:=κ) ht (hu1 e) (hu0 e)]
      · rw [ite_eq_right hl,sub_zero,good_capacity_unsaturated ha (le_of_not_gt hl) ht1]
        linarith
    · simp only [booleanResponse,hg,not_false_eq_true,ite_true, if_true,ite_false, if_false,
        bad_capacity_loss ht ha (hu1 e)]
      split_ifs <;> linarith
  have hs := sum_le_sum hb
  simp only [sum_sub_distrib,←sum_filter,sum_const,nsmul_eq_mul] at hs
  rw [sum_sub_distrib]
  nlinarith only [hs]

lemma large_count_bound (A : Finset (Fin m)) (u : Fin m → ℝ) (hu : ∀e, 0 ≤ u e) :
    (((A.filter (fun e => 1/2<u e)).card:ℝ)) ≤ 2*∑e ∈ A, u e := by
  have hb (e : Fin m) (_ : e ∈ A) : (if 1/2<u e then (1:ℝ) else 0) ≤ 2*u e := by
    split_ifs with hh <;> linarith [hu e]
  have hs := sum_le_sum hb
  rw [←sum_filter,sum_const,nsmul_eq_mul,mul_one,←mul_sum] at hs
  exact hs

lemma active_capacity_sum_le (F : Finset (Fin m)) (u : Fin m → ℝ) (hu : ∀e, 0 ≤ u e)
    {κ : ℝ} (hκ : 0 ≤ κ) :
    (∑e ∈ F ∩ Partitions.active u, u e) ≤ ∑e ∈ F, (u e+κ) := by
  calc
    _ ≤ ∑e ∈ F, u e := sum_le_sum_of_subset_of_nonneg inter_subset_left (fun e _ _ => hu e)
    _ ≤ _ := sum_le_sum (fun e _ => le_add_of_nonneg_right hκ)

lemma many_edges_half_unsaturated (F : Finset (Fin m)) (u : Fin m → ℝ)
    (hu0 : ∀e, 0 ≤ u e) {κ r d Q : ℝ} (hκ : 0 ≤ κ) (hr : 1 ≤ r) (hd : 2 ≤ d)
    (hQ : Q ≤ r) (hnear : (∑e ∈ F, (u e+κ)) ≤ Q*(d-1)+1)
    (hmany : 8*r*(d-1) < ((F ∩ Partitions.active u).card:ℝ)) :
    (((F ∩ Partitions.active u).filter (fun e => 1/2<u e)).card:ℝ) ≤
      ((F ∩ Partitions.active u).card:ℝ)/2 := by
  have h1 := large_count_bound (F ∩ Partitions.active u) u hu0
  have h2 := active_capacity_sum_le F u hu0 hκ
  have h3 := mul_le_mul_of_nonneg_right hQ (by linarith : 0 ≤ d-1)
  have hprod : 1 ≤ r*(d-1) := by nlinarith only [mul_nonneg (sub_nonneg.mpr hr) (by linarith : 0 ≤ d-2),hr,hd]
  nlinarith only [h1,h2,h3,hnear,hmany,hprod]

lemma few_edges_loss_bound (F : Finset (Fin m)) (u : Fin m → ℝ)
    (hu0 : ∀e, 0 ≤ u e) (hu1 : ∀e, u e ≤ 1) (good : Fin m → Prop)
    {κ t r d ε g : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε) (hεg : 32*ε ≤ g)
    (hr : 0 ≤ r) (hd : 1 ≤ d)
    (hbad : (((F ∩ Partitions.active u).filter (fun e => ¬good e)).card:ℝ) ≤
      ε*(F ∩ Partitions.active u).card)
    (hfew : ((F ∩ Partitions.active u).card:ℝ) ≤ 8*r*(d-1)) :
    -g*r*t*(d-1) ≤ (∑e ∈ F, lowerCapacity κ t (u e) (booleanResponse good e))-
      (∑e ∈ F, (u e+κ)) := by
  have h1 := capacity_change_loss F u hu0 hu1 good (κ:=κ) ht
  have h2 := mul_le_mul_of_nonneg_left hfew hε
  have h3 := mul_le_mul_of_nonneg_left (hbad.trans h2) (by linarith : 0 ≤ 4*t)
  have h4 := mul_le_mul_of_nonneg_right hεg (mul_nonneg (mul_nonneg hr ht) (by linarith : 0 ≤ d-1))
  nlinarith only [h1,h3,h4]

lemma many_edges_gain_bound (F : Finset (Fin m)) (u : Fin m → ℝ)
    (hu0 : ∀e, 0 ≤ u e) (hu1 : ∀e, u e ≤ 1) (good : Fin m → Prop)
    {κ t r d Q ε : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1/2) (hκ : 0 ≤ κ)
    (hr : 1 ≤ r) (hd : 2 ≤ d) (hQ : Q ≤ r) (hε : ε ≤ 1/10)
    (hnear : (∑e ∈ F, (u e+κ)) ≤ Q*(d-1)+1)
    (hbad : (((F ∩ Partitions.active u).filter (fun e => ¬good e)).card:ℝ) ≤
      ε*(F ∩ Partitions.active u).card)
    (hmany : 8*r*(d-1) < ((F ∩ Partitions.active u).card:ℝ)) :
    0 ≤ (∑e ∈ F, lowerCapacity κ t (u e) (booleanResponse good e))-
      (∑e ∈ F, (u e+κ)) := by
  have h1 := capacity_change_gain F u hu0 hu1 good (κ:=κ) ht ht1
  have h2 := many_edges_half_unsaturated F u hu0 hκ hr hd hQ hnear hmany
  have h3 := mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg (F ∩ Partitions.active u).card)
  have h4 : 0 ≤ ((F ∩ Partitions.active u).card:ℝ)-
      (((F ∩ Partitions.active u).filter (fun e => 1/2<u e)).card:ℝ)-
      5*(((F ∩ Partitions.active u).filter (fun e => ¬good e)).card:ℝ) := by
    linarith only [h2,h3,hbad]
  exact (mul_nonneg ht h4).trans h1

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_PartitionUncrossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partition uncrossing. -/

section

namespace AlgorithmicThinTrees.Partitions
noncomputable section
open Finset
open scoped Classical

variable {V X : Type*} [Fintype V]

lemma certificates_isClosed (C : Set X) (f : Setoid V → X → ℝ) (b : ℝ) :
    IsClosed (Certificates C f b) := by
  have h0 : IsClosed {w : Setoid V → ℝ | ∀p, 0 ≤ w p} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun p => isClosed_le continuous_const (continuous_apply p))
  have h1 : IsClosed {w : Setoid V → ℝ | (∑p, w p)=1} :=
    isClosed_eq (continuous_finsetSum _ (fun p _ => continuous_apply p)) continuous_const
  have h2 : IsClosed {w : Setoid V → ℝ | ∀x ∈ C, (∑p, w p*f p x) ≤ b} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun x => isClosed_iInter (fun _ => isClosed_le
      (continuous_finsetSum _ (fun p _ => (continuous_apply p).mul_const _)) continuous_const))
  exact h0.inter (h1.inter h2)

lemma certificates_compact (C : Set X) (f : Setoid V → X → ℝ) (b : ℝ) :
    IsCompact (Certificates C f b) := by
  have hbox : IsCompact {w : Setoid V → ℝ | ∀p, w p ∈ Set.Icc (0:ℝ) 1} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  apply hbox.of_isClosed_subset (certificates_isClosed C f b)
  intro w hw p
  refine ⟨hw.1 p,?_⟩
  have hh := single_le_sum (fun q _ => hw.1 q) (mem_univ p)
  exact hh.trans_eq hw.2.1

omit [Fintype V] in
lemma uncrossWeight_nonneg (w : Setoid V → ℝ) (hw : ∀i, 0 ≤ w i)
    {p q : Setoid V} (hpq : p ≠ q) {δ : ℝ} (hδ : 0 ≤ δ)
    (hp : δ ≤ w p) (hq : δ ≤ w q) : ∀i, 0 ≤ uncrossWeight w p q δ i := by
  intro i
  have hmeet : 0 ≤ (if i=p ⊓ q then δ else 0) := by split_ifs <;> positivity
  have hjoin : 0 ≤ (if i=p ⊔ q then δ else 0) := by split_ifs <;> positivity
  unfold uncrossWeight
  by_cases hip : i=p
  · subst i
    simp only [ite_true, if_true,ite_eq_right hpq]
    linarith
  · by_cases hiq : i=q
    · subst i
      simp only [ite_eq_right hip,ite_true, if_true]
      linarith
    · simp only [ite_eq_right hip,ite_eq_right hiq,sub_zero]
      linarith [hw i]

lemma uncrossWeight_dot (w g : Setoid V → ℝ) (p q : Setoid V) (δ : ℝ) :
    (∑i, uncrossWeight w p q δ i*g i) =
      (∑i, w i*g i)+δ*g (p ⊓ q)+δ*g (p ⊔ q)-δ*g p-δ*g q := by
  simp [uncrossWeight,add_mul,sub_mul,sum_add_distrib,sum_sub_distrib,ite_mul]

lemma uncrossWeight_sum (w : Setoid V → ℝ) (p q : Setoid V) (δ : ℝ) :
    (∑i, uncrossWeight w p q δ i)=∑i, w i := by
  have hh := uncrossWeight_dot w (fun _ => 1) p q δ
  simpa only [mul_one,add_sub_cancel_right] using hh

theorem chain_certificate (C : Set X) (f : Setoid V → X → ℝ) (b : ℝ)
    (hsub : ∀x ∈ C, ∀p q, f (p ⊓ q) x+f (p ⊔ q) x ≤ f p x+f q x)
    (hne : (Certificates C f b).Nonempty) :
    ∃w ∈ Certificates C f b, IsChain (· ≤ ·) {p | 0 < w p} := by
  let Φ : (Setoid V → ℝ) → ℝ := fun w => ∑p, w p*potential p
  have hΦ : Continuous Φ := continuous_finsetSum _
    (fun p _ => (continuous_apply p).mul_const _)
  obtain ⟨w,hw,hmax⟩ := (certificates_compact C f b).exists_isMaxOn hne hΦ.continuousOn
  refine ⟨w,hw,?_⟩
  intro p hp q hq _
  by_contra hincomp
  have hpq : ¬p ≤ q := fun h => hincomp (Or.inl h)
  have hqp : ¬q ≤ p := fun h => hincomp (Or.inr h)
  have hnepq : p ≠ q := fun he => hpq (he ▸ le_rfl)
  let δ := min (w p) (w q)
  have hδ : 0 < δ := lt_min hp hq
  let w' := uncrossWeight w p q δ
  have hw' : w' ∈ Certificates C f b := by
    refine ⟨uncrossWeight_nonneg w hw.1 hnepq hδ.le (min_le_left _ _) (min_le_right _ _),?_,?_⟩
    · rw [uncrossWeight_sum]
      exact hw.2.1
    · intro x hx
      dsimp [w']
      rw [uncrossWeight_dot]
      have hh := mul_le_mul_of_nonneg_left (hsub x hx p q) hδ.le
      linarith [hw.2.2 x hx]
  have hgain := mul_pos hδ (sub_pos.mpr (potential_uncross hpq hqp))
  have hdot : Φ w' = Φ w+δ*potential (p ⊓ q)+δ*potential (p ⊔ q)-δ*potential p-δ*potential q :=
    uncrossWeight_dot w potential p q δ
  have hmax' := (isMaxOn_iff.mp hmax) w' hw'
  nlinarith only [hgain,hdot,hmax']

variable [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]

theorem feasible_of_chain_feasible (C : Set X) (hcompact : IsCompact C)
    (hne : C.Nonempty) (hconvex : Convex ℝ C) (f : Setoid V → X → ℝ)
    (hcontinuous : ∀p, ContinuousOn (f p) C)
    (hconcave : ∀p, ConcaveOn ℝ C (f p))
    (hsub : ∀x ∈ C, ∀p q, f (p ⊓ q) x+f (p ⊔ q) x ≤ f p x+f q x)
    (hchains : ∀J : Finset (Setoid V), IsChain (· ≤ ·) (J : Set (Setoid V)) →
      ∃x ∈ C, ∀p ∈ J, 0 ≤ f p x) :
    ∃x ∈ C, ∀p, 0 ≤ f p x := by
  by_contra hnone
  obtain ⟨ε,hε,w,hw,hws,hbound⟩ := ConvexAlternative.compact_concave_alternative C
    hcompact hne hconvex f hcontinuous hconcave hnone
  obtain ⟨v,hv,hvchain⟩ := chain_certificate C f (-ε) hsub ⟨w,hw,hws,hbound⟩
  let J := univ.filter (fun p => 0 < v p)
  have hJ : IsChain (· ≤ ·) (J : Set (Setoid V)) := by
    simpa only [J,coe_filter,coe_univ,Set.sep_univ,mem_univ,true_and] using hvchain
  obtain ⟨x,hx,hxJ⟩ := hchains J hJ
  have hnon : 0 ≤ ∑p, v p*f p x := by
    apply sum_nonneg
    intro p _
    by_cases hp : 0 < v p
    · exact mul_nonneg hp.le (hxJ p (mem_filter.mpr ⟨mem_univ p,hp⟩))
    · have he : v p=0 := le_antisymm (le_of_not_gt hp) (hv.1 p)
      simp [he]
  linarith only [hnon,hv.2.2 x hx,hε]

end
end AlgorithmicThinTrees.Partitions
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Feasibility
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_baselineQ _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_stepQ
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation feasibility. -/

section

namespace AlgorithmicThinTrees.Partitions
noncomputable section
open Finset
open scoped Classical

lemma slack_top {V E : Type*} [Fintype V] [Nonempty V] [Fintype E]
    (left right : E → V) (w : E → ℝ) (Q : ℝ) :
    slack left right w Q ⊤=0 := by
  simp [slack,capacity,crossingIndicator,partCount_top]

end
end AlgorithmicThinTrees.Partitions

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Finset Matrix StrongThinTree StrongThinTree.MultiGraph
open Partitions
open scoped Classical MatrixOrder Matrix.Norms.Elementwise

variable {n m : ℕ}

lemma capacity_change_worst (F : Finset (Fin m)) (u : Fin m → ℝ)
    (hu0 : ∀e, 0 ≤ u e) (hu1 : ∀e, u e ≤ 1) (good : Fin m → Prop)
    {κ t : ℝ} (ht : 0 ≤ t) :
    -4*t*m ≤ (∑e ∈ F, lowerCapacity κ t (u e) (booleanResponse good e))-
      (∑e ∈ F, (u e+κ)) := by
  have hh := capacity_change_loss F u hu0 hu1 good (κ:=κ) ht
  have hcard : (((F ∩ active u).filter (fun e => ¬good e)).card:ℝ) ≤ m := by
    exact_mod_cast (show ((F ∩ active u).filter (fun e => ¬good e)).card ≤ m by
      simpa only [Fintype.card_fin] using card_le_univ ((F ∩ active u).filter (fun e => ¬good e)))
  have hm := mul_le_mul_of_nonpos_left hcard (by linarith : -4*t ≤ 0)
  exact hm.trans hh

lemma continuation_fraction_cutoff :
    ∃r0 : ℕ, 8 ≤ r0 ∧ ∀r : ℕ, r0 ≤ r →
      (r:ℝ)^(-1/3:ℝ) ≤ 1/10 ∧ 32*(r:ℝ)^(-1/3:ℝ) ≤ (r:ℝ)^(-1/8:ℝ) := by
  open Filter in
  have he : ∀ᶠ x : ℝ in atTop,
      10*x^(-1/3:ℝ) ≤ x^(0:ℝ) ∧ 32*x^(-1/3:ℝ) ≤ x^(-1/8:ℝ) :=
    (ShortcutNumeric.eventually_const_mul_rpow_le_rpow 10 (by norm_num)).and
      (ShortcutNumeric.eventually_const_mul_rpow_le_rpow 32 (by norm_num))
  open Filter in
  have heN : ∀ᶠ r : ℕ in atTop,
      10*(r:ℝ)^(-1/3:ℝ) ≤ (r:ℝ)^(0:ℝ) ∧
        32*(r:ℝ)^(-1/3:ℝ) ≤ (r:ℝ)^(-1/8:ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun r : ℕ => (r:ℝ)) atTop atTop).eventually he
  obtain ⟨r0,hr0⟩ := heN.exists_forall_of_atTop
  refine ⟨max 8 r0,le_max_left _ _,?_⟩
  intro r hr
  have hh := hr0 r ((le_max_right _ _).trans hr)
  refine ⟨?_,hh.2⟩
  rw [Real.rpow_zero] at hh
  linarith only [hh.1]

lemma chain_continuation_feasible (H : MultiGraph n m) (hn : 2 ≤ n) (_hconn : H.Connected univ)
    (u : Fin m → ℝ) (hu0 : ∀e, 0 ≤ u e) (hu1 : ∀e, u e ≤ 1)
    {r : ℕ} {κ t Q s g : ℝ}
    (hr : 8 ≤ r) (hκ : 0 ≤ κ) (hκm : κ*m < 1)
    (ht : 0 ≤ t) (ht1 : t ≤ 1/2) (htm : 4*t*m ≤ 1)
    (hQ : 3*(r:ℝ)/4 ≤ Q) (hQr : Q ≤ r) (hg : 0 ≤ g)
    (hε : (r:ℝ)^(-1/3:ℝ) ≤ 1/10) (hεg : 32*(r:ℝ)^(-1/3:ℝ) ≤ g)
    (_hs : 0 < s) (_hsr : s ≤ (r:ℝ)^(1/4:ℝ))
    (hinv : ∀p, 0 ≤ slack H.left H.right (fun e => u e+κ) Q p)
    (hgeom : ∀J : Finset (Setoid (Fin n)), IsChain (· ≤ ·) (J : Set (Setoid (Fin n))) →
      (∀p ∈ J, ∀A ∈ parts p, (H.restrict (active u)).EdgeConnectedReal A (r/2:ℕ)) →
      (H.restrict (active u)).EdgeConnectedReal univ (r/2:ℕ) →
      ∃Y ∈ metricDomain H, CenteredPositive Y ∧ ∀p ∈ J,
        (((crossing H p ∩ active u).filter (fun e =>
          ¬ (6*s) • vecMulVec (H.incidence e) (H.incidence e) ≤ Y)).card:ℝ) ≤
          (r:ℝ)^(-1/3:ℝ)*(crossing H p ∩ active u).card)
    (J : Finset (Setoid (Fin n))) (hJ : IsChain (· ≤ ·) (J : Set (Setoid (Fin n)))) :
    ∃x ∈ admissible H s u, ∀p ∈ J, 0 ≤ responseSlack H κ t (Q-g*r*t) u p x := by
  have : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  have hrR : (8:ℝ) ≤ r := by exact_mod_cast hr
  have hQ0 : 0 ≤ Q := by linarith only [hrR,hQ]
  have hh : ((r/2:ℕ):ℝ) ≤ Q-2 := by
    have hdiv : (2:ℝ)*((r/2:ℕ):ℝ) ≤ r := by exact_mod_cast Nat.mul_div_le r 2
    linarith only [hdiv,hrR,hQ]
  let K := J.filter (fun p => p ≠ ⊤ ∧ slack H.left H.right (fun e => u e+κ) Q p ≤ 1)
  have hK : IsChain (· ≤ ·) (K : Set (Setoid (Fin n))) := hJ.mono (by
    intro p hp
    exact (mem_filter.mp hp).1)
  have hlocal : ∀p ∈ K, ∀A ∈ parts p, (H.restrict (active u)).EdgeConnectedReal A (r/2:ℕ) := by
    intro p hp A hA
    exact near_tight_locally_connected H u hu0 hu1 hκ hκm hQ0 hh hinv (mem_filter.mp hp).2.2 hA
  have hroot : (H.restrict (active u)).EdgeConnectedReal univ (r/2:ℕ) :=
    near_tight_locally_connected H u hu0 hu1 hκ hκm hQ0 hh hinv
      (by rw [slack_top]; norm_num) (by rw [parts_top]; exact mem_singleton_self _)
  obtain ⟨Y,hY,hYP,hbad⟩ := hgeom K hK hlocal hroot
  let good : Fin m → Prop := fun e => (6*s) • vecMulVec (H.incidence e) (H.incidence e) ≤ Y
  let y := booleanResponse good
  have hresponse : (Y,y) ∈ admissible H s u := by
    refine ⟨hY,booleanResponse_bounds good,?_⟩
    intro e _
    by_cases he : good e
    · change (6*s*booleanResponse good e) • vecMulVec (H.incidence e) (H.incidence e) ≤ Y
      simpa only [booleanResponse,ite_eq_left he,mul_one] using he
    · change (6*s*booleanResponse good e) • vecMulVec (H.incidence e) (H.incidence e) ≤ Y
      simp only [booleanResponse,ite_eq_right he,mul_zero,zero_smul]
      exact Matrix.nonneg_iff_posSemidef.mpr (domain_psd H hY)
  refine ⟨(Y,y),hresponse,?_⟩
  intro p hp
  by_cases htop : p=⊤
  · subst p
    simp only [responseSlack,slack_top,le_refl]
  have hd : (2:ℝ) ≤ partCount p := by exact_mod_cast two_le_partCount htop
  have hβ : 0 ≤ g*(r:ℝ)*t*((partCount p:ℝ)-1) :=
    mul_nonneg (mul_nonneg (mul_nonneg hg (Nat.cast_nonneg r)) ht) (by linarith)
  have hcap := hinv p
  unfold slack at hcap
  rw [capacity_eq_sum] at hcap
  unfold responseSlack slack
  rw [capacity_eq_sum]
  change 0 ≤ (∑e ∈ crossing H p, lowerCapacity κ t (u e) (booleanResponse good e))-
    (Q-g*r*t)*((partCount p:ℝ)-1)
  by_cases hnear : slack H.left H.right (fun e => u e+κ) Q p ≤ 1
  · have hKp : p ∈ K := mem_filter.mpr ⟨hp,htop,hnear⟩
    have hb : (((crossing H p ∩ active u).filter (fun e => ¬good e)).card:ℝ) ≤
        (r:ℝ)^(-1/3:ℝ)*(crossing H p ∩ active u).card := hbad p hKp
    have hnear' : (∑e ∈ crossing H p, (u e+κ)) ≤ Q*((partCount p:ℝ)-1)+1 := by
      unfold slack at hnear
      rw [capacity_eq_sum] at hnear
      linarith only [hnear]
    by_cases hfew : ((crossing H p ∩ active u).card:ℝ) ≤ 8*r*((partCount p:ℝ)-1)
    · have hloss := few_edges_loss_bound (crossing H p) u hu0 hu1 good (κ:=κ) ht
        (Real.rpow_nonneg (Nat.cast_nonneg r) (-1/3:ℝ)) hεg (Nat.cast_nonneg r)
        (by linarith : 1 ≤ (partCount p:ℝ)) hb hfew
      nlinarith only [hloss,hcap]
    · have hgain := many_edges_gain_bound (crossing H p) u hu0 hu1 good (κ:=κ) ht ht1 hκ
        (by linarith : (1:ℝ) ≤ r) hd hQr hε hnear' hb (lt_of_not_ge hfew)
      nlinarith only [hgain,hβ,hcap]
  · have hfar : 1 < (∑e ∈ crossing H p, (u e+κ))-Q*((partCount p:ℝ)-1) := by
      have hh := lt_of_not_ge hnear
      simpa only [slack,capacity_eq_sum] using hh
    have hloss := capacity_change_worst (crossing H p) u hu0 hu1 good (κ:=κ) ht
    nlinarith only [hloss,hβ,hfar,htm]

lemma continuation_parameters (m : ℕ) :
    0 < continuationBaseline m ∧ continuationBaseline m ≤ 1 ∧
    continuationBaseline m*m < 1 ∧
    0 ≤ continuationStep m ∧ continuationStep m ≤ 1/32 ∧
    4*continuationStep m ≤ continuationBaseline m ∧ 4*continuationStep m*m ≤ 1 := by
  have hmp : (0:ℝ) < m+1 := by positivity
  have hκ : 0 < continuationBaseline m := one_div_pos.mpr hmp
  have hκeq : continuationBaseline m*((m:ℝ)+1)=1 := div_mul_cancel₀ 1 (ne_of_gt hmp)
  have hκm : 0 ≤ continuationBaseline m*m := mul_nonneg hκ.le (Nat.cast_nonneg m)
  have hκ1 : continuationBaseline m ≤ 1 := by nlinarith only [hκeq,hκm]
  have hκm1 : continuationBaseline m*m < 1 := by nlinarith only [hκeq,hκ]
  refine ⟨hκ,hκ1,hκm1,?_,?_,?_,?_⟩ <;> unfold continuationStep <;>
    nlinarith only [hκ,hκ1,hκm1,hκm]

theorem feasible_continuation_response :
    ∃r0 : ℕ, 8 ≤ r0 ∧ ∀r : ℕ, r0 ≤ r →
      ∀(n m : ℕ) (H : MultiGraph n m), 2 ≤ n → H.Connected univ →
      ∀(u : Fin m → ℝ), (∀e, 0 ≤ u e) → (∀e, u e ≤ 1) →
      ∀(s Q g : ℝ), 0 < s → s ≤ (r:ℝ)^(1/4:ℝ) →
      3*(r:ℝ)/4 ≤ Q → Q ≤ r →
      (r:ℝ)^(-1/8:ℝ) ≤ g → g ≤ 2*(r:ℝ)^(-1/8:ℝ) →
      (∀p, 0 ≤ slack H.left H.right (fun e => u e+continuationBaseline m) Q p) →
      ∃x ∈ admissible H s u,
        ∀p, 0 ≤ responseSlack H (continuationBaseline m) (continuationStep m)
          (Q-g*r*continuationStep m) u p x := by
  obtain ⟨r0,hr0,hgeom⟩ := finite_chain_response
  obtain ⟨r1,hr1,hfrac⟩ := continuation_fraction_cutoff
  refine ⟨max r0 r1,hr1.trans (le_max_right _ _),?_⟩
  intro r hr n m H hn hconn u hu0 hu1 s Q g hs hsr hQ hQr hg hgg hinv
  have hr0' : r0 ≤ r := (le_max_left _ _).trans hr
  have hr1' : r1 ≤ r := (le_max_right _ _).trans hr
  have hr8 : 8 ≤ r := hr1.trans hr1'
  have hrR : (8:ℝ) ≤ r := by exact_mod_cast hr8
  have hg0 : 0 ≤ g := (Real.rpow_nonneg (Nat.cast_nonneg r) _).trans hg
  have hg2 : g ≤ 2 := by
    have hp := Real.rpow_le_one_of_one_le_of_nonpos (by linarith : (1:ℝ) ≤ r)
      (by norm_num : (-1/8:ℝ) ≤ 0)
    linarith only [hp,hgg]
  obtain ⟨hκ,hκ1,hκm,ht,ht1,hκt,htm⟩ := continuation_parameters m
  have hq : 0 ≤ Q-g*r*continuationStep m := by
    have hgt := mul_le_mul hg2 ht1 ht (by norm_num : (0:ℝ) ≤ 2)
    have hh := mul_le_mul_of_nonneg_right hgt (Nat.cast_nonneg r)
    nlinarith only [hh,hrR,hQ]
  have hchains : ∀J : Finset (Setoid (Fin n)), IsChain (· ≤ ·) (J : Set (Setoid (Fin n))) →
      ∃x ∈ admissible H s u, ∀p ∈ J, 0 ≤ responseSlack H (continuationBaseline m)
        (continuationStep m) (Q-g*r*continuationStep m) u p x := by
    intro J hJ
    apply chain_continuation_feasible H hn hconn u hu0 hu1 hr8 hκ.le hκm ht
      (by linarith : continuationStep m ≤ 1/2) htm hQ hQr hg0
      (hfrac r hr1').1 ((hfrac r hr1').2.trans hg) hs hsr hinv _ J hJ
    intro K hK hlocal hroot
    exact hgeom r hr0' n m H hn hconn (active u) K hK hlocal hroot s hs hsr
  exact feasible_of_chain_feasible (admissible H s u) (admissible_compact H (by omega) s u)
    (admissible_nonempty H s u) (admissible_convex H s u)
    (responseSlack H (continuationBaseline m) (continuationStep m) (Q-g*r*continuationStep m) u)
    (fun p => (responseSlack_continuous H _ _ _ u p).continuousOn)
    (fun p => responseSlack_concave H _ _ _ s u p)
    (fun _ hx p q => responseSlack_submodular H u ht hκt hq hx p q) hchains

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_SpectralSize
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_boundQ _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_errorQ _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_radiusQ _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_sizeQ
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spectral size. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder

variable {n m : ℕ}

lemma graphSize_pos : 0 < graphSize n m := by
  dsimp [graphSize]
  positivity

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Interior
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_baselineQ _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_boundQ _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_errorQ _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_radiusQ _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_sizeQ
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation interior. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped Classical MatrixOrder Matrix.Norms.Elementwise

variable {n m : ℕ}

lemma scaled_inverse_power {P c : ℝ} (hP : 0 < P) (a b : ℕ) (hc : c ≤ P^b) :
    c*P^(-((a+b : ℕ) : ℤ)) ≤ P^(-(a : ℤ)) := by
  have h := mul_le_mul_of_nonneg_right hc (zpow_nonneg hP.le (-((a+b : ℕ) : ℤ)))
  calc
    _ ≤ P^b*P^(-((a+b : ℕ) : ℤ)) := h
    _ = _ := by
      rw [←zpow_natCast,←zpow_add₀ (ne_of_gt hP)]
      congr 1
      push_cast
      ring

lemma connected_size_five (H : MultiGraph n m) (hn : 2 ≤ n) (hc : H.Connected univ) :
    5 ≤ graphSize n m := by
  have hm : 0 < m := by
    have hproper : ({⟨0,by omega⟩} : Finset (Fin n)) ≠ univ := by
      intro h
      have hh := congrArg Finset.card h
      simp only [card_singleton,card_univ,Fintype.card_fin] at hh
      omega
    obtain ⟨e,_⟩ := hc _ (singleton_nonempty _) hproper
    exact Nat.zero_lt_of_lt e.isLt
  dsimp [graphSize]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  linarith

lemma baseline_lower : (graphSize n m)⁻¹ ≤ continuationBaseline m := by
  rw [continuationBaseline,one_div]
  exact (inv_le_inv₀ graphSize_pos (by positivity : (0 : ℝ) < m+1)).mpr (by
    dsimp [graphSize]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    linarith)

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Flow_RootedFlow
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rooted flow. -/

section

namespace AlgorithmicThinTrees.Orientations
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical
variable {n m : ℕ}

lemma internal_le_out (G : MultiGraph n m) {x a b : Fin m → ℝ}
    (ha : ∀e, 0 ≤ a e) (hb : ∀e, 0 ≤ b e) (he : ∀e, x e ≤ a e+b e)
    (S : Finset (Fin n)) :
    (∑e ∈ univ.filter (fun e => G.left e ∈ S ∧ G.right e ∈ S), x e) ≤ ∑v ∈ S, out G a b v := by
  rw [sum_filter]
  simp only [out]
  rw [sum_comm]
  apply sum_le_sum
  intro e he'
  have hsum : (∑v ∈ S, ((if G.left e=v then a e else 0)+(if G.right e=v then b e else 0)))=
      (if G.left e ∈ S then a e else 0)+(if G.right e ∈ S then b e else 0) := by
    rw [sum_add_distrib]
    simp only [sum_ite_eq]
  rw [hsum]
  by_cases hl : G.left e ∈ S <;> by_cases hr : G.right e ∈ S
  · simpa only [hl,hr,and_self,ite_true, if_true] using he e
  · simpa only [hl,hr,and_false,ite_false, if_false,ite_true, if_true,add_zero] using ha e
  · simpa only [hl,hr,false_and,ite_false, if_false,ite_true, if_true,zero_add] using hb e
  · simp [hl,hr]

end
end AlgorithmicThinTrees.Orientations
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Flow_RootedRelaxation
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_a _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_b _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_mat _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_mul _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_x _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_y _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_z _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.flow_a _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.flow_b _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.flow_x
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rooted relaxation. -/

section

namespace AlgorithmicThinTrees.Orientations
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped Classical
variable {n m : ℕ}

lemma parts_card {V : Type*} [Fintype V] (p : Setoid V) : (parts p).card=partCount p := by
  let f : Quotient p → parts p := Quotient.lift
    (fun v => ⟨block p v,block_mem_parts p v⟩)
    (fun a b h => Subtype.ext ((block_eq_iff p a b).mpr h))
  have hf : Function.Bijective f := by
    constructor
    · intro a b
      induction a,b using Quotient.inductionOn₂ with
      | h a b =>
        intro he
        exact Quotient.sound ((block_eq_iff p a b).mp (congrArg Subtype.val he))
    · intro A
      obtain ⟨v,hv⟩ := (mem_parts p A.val).mp A.property
      exact ⟨Quotient.mk p v,Subtype.ext hv⟩
  exact (Fintype.card_coe (parts p)).symm.trans (Fintype.card_congr (Equiv.ofBijective f hf)).symm

lemma parts_sum_card (p : Setoid (Fin n)) : ∑A ∈ parts p, A.card=n := by
  have h := card_biUnion (s:=parts p) (t:=id) 
    (fun A hA B hB hAB => parts_disjoint p hA hB hAB)
  have hcov : (parts p).biUnion id=(univ : Finset (Fin n)) := by
    ext v
    simp only [mem_biUnion,mem_univ,iff_true]
    exact ⟨block p v,block_mem_parts p v,self_mem_block p v⟩
  rw [hcov,card_univ,Fintype.card_fin] at h
  exact h.symm

lemma block_eq_of_part {p : Setoid (Fin n)} {S : Finset (Fin n)}
    (hS : S ∈ parts p) {v : Fin n} (hv : v ∈ S) : S=block p v := by
  obtain ⟨w,rfl⟩ := (mem_parts p S).mp hS
  exact (block_eq_iff p w v).mpr ((mem_block p w v).mp hv)

lemma internal_partition_accounting (G : MultiGraph n m) (x : Fin m → ℝ)
    (p : Setoid (Fin n)) :
    (∑S ∈ parts p, ∑e ∈ univ.filter (fun e => G.left e ∈ S ∧ G.right e ∈ S), x e)+
      capacity G.left G.right x p = ∑e, x e := by
  simp only [sum_filter,capacity]
  rw [sum_comm,←sum_add_distrib]
  apply sum_congr rfl
  intro e he
  have hi : (∑S ∈ parts p, if G.left e ∈ S ∧ G.right e ∈ S then x e else 0)=
      if p (G.left e) (G.right e) then x e else 0 := by
    rw [sum_eq_single (block p (G.left e))]
    · simp only [self_mem_block,mem_block,true_and]
    · intro S hS hSne
      apply ite_eq_right
      rintro ⟨hl,hr⟩
      exact hSne (block_eq_of_part hS hl)
    · intro h
      exact (h (block_mem_parts p (G.left e))).elim
  rw [hi,crossingIndicator]
  split_ifs <;> ring

lemma sum_root_budget {S : Finset (Fin n)} {r : Fin n} (hr : r ∈ S) (qbar ε : ℝ) :
    (∑v ∈ S, if v=r then ε else qbar) = qbar*((S.card:ℝ)-1)+ε := by
  have he (v : Fin n) : (if v=r then ε else qbar) =
      (if v=r then ε-qbar else 0)+qbar := by split_ifs <;> ring
  simp only [he,sum_add_distrib,sum_ite_eq',hr,ite_true, if_true,sum_const,nsmul_eq_mul]
  ring

lemma internal_flow_bound (G : MultiGraph n m) (c : Fin m → ℝ) {qbar ε : ℝ}
    {F : FlowPoint n m} (hF : F.Feasible G c qbar ε)
    (S : Finset (Fin n)) (hS : S.Nonempty) :
    (∑e ∈ univ.filter (fun e => G.left e ∈ S ∧ G.right e ∈ S), F.x e) ≤
      qbar*((S.card:ℝ)-1)+ε := by
  obtain ⟨r,hr⟩ := hS
  calc
    _ ≤ ∑v ∈ S, out G (F.a r) (F.b r) v :=
      internal_le_out G (fun e => (hF.2.1 r e).1) (fun e => (hF.2.1 r e).2.1)
        (fun e => (hF.2.1 r e).2.2) S
    _ ≤ ∑v ∈ S, if v=r then ε else qbar := sum_le_sum fun v _ => hF.2.2.1 r v
    _ = _ := sum_root_budget hr qbar ε

lemma flow_partition_bound (G : MultiGraph n m) (c : Fin m → ℝ) {qbar ε : ℝ}
    {F : FlowPoint n m} (hF : F.Feasible G c qbar ε) (p : Setoid (Fin n)) :
    qbar*((partCount p:ℝ)-1)-ε*((partCount p:ℝ)+1) ≤ capacity G.left G.right c p := by
  have hi := sum_le_sum (s:=parts p) (fun S hS => internal_flow_bound G c hF S
    ((parts_partition p).1 S hS).1)
  have hs : (∑S ∈ parts p, (qbar*((S.card:ℝ)-1)+ε))=
      qbar*((n:ℝ)-partCount p)+ε*partCount p := by
    simp only [mul_sub,mul_one,sum_add_distrib,sum_sub_distrib,←mul_sum,sum_const,nsmul_eq_mul]
    rw [←Nat.cast_sum,parts_sum_card,parts_card]
    ring
  rw [hs] at hi
  have hcross : capacity G.left G.right F.x p ≤ capacity G.left G.right c p :=
    sum_le_sum fun e _ => mul_le_mul_of_nonneg_right (hF.1 e).2 (crossingIndicator_nonneg _ _ _)
  have htotal := hF.2.2.2
  have haccount := internal_partition_accounting G F.x p
  linarith

theorem relaxed_flow_implies_partitions (G : MultiGraph n m) (hn : 0 < n)
    (c : Fin m → ℝ) {q ε : ℝ} (hε : 0 ≤ ε) {F : FlowPoint n m}
    (hF : F.Feasible G c (q+4*ε) ε) :
    ∀p, 0 ≤ slack G.left G.right c q p := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  intro p
  by_cases hp : p=⊤
  · subst p
    simp [slack,capacity,crossingIndicator,partCount_top]
  · have hd : (2:ℝ) ≤ partCount p := by exact_mod_cast two_le_partCount hp
    have hb := flow_partition_bound G c hF p
    have he : 0 ≤ ε*(3*(partCount p:ℝ)-5) := mul_nonneg hε (by linarith)
    dsimp [slack]
    nlinarith only [hb,he]

end
end AlgorithmicThinTrees.Orientations
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Coordinates
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation coordinates. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Orientations

variable {n m : ℕ}

lemma rational_real (v : Fin (dimension n m) → ℚ) :
    (rational v).real=step (fun i => (v i:ℝ)) := rfl

lemma close_step_flow (c : StepFree n m) (F : FlowPoint n m)
    (v : Fin (dimension n m) → ℝ) {ρ : ℝ}
    (h : ∀i, |v i-encode c F i| ≤ ρ) :
    (step v).Close c ρ ∧ (flow v).Close F ρ := by
  refine ⟨⟨?_,?_,?_,?_⟩,⟨?_,?_,?_⟩⟩
  · intro i j
    simpa only [step,flow,StepFree.multiplier,StepFree.y,StepFree.z,rawMatrix,multiplier,y,z,flowX,flowA,flowB,encode_mat] using h (matIndex i j)
  · intro ijk
    simpa only [step,flow,StepFree.multiplier,StepFree.y,StepFree.z,rawMatrix,multiplier,y,z,flowX,flowA,flowB,encode_mul] using h (mulIndex ijk.val)
  · intro e
    simpa only [step,flow,StepFree.multiplier,StepFree.y,StepFree.z,rawMatrix,multiplier,y,z,flowX,flowA,flowB,encode_y] using h (edgeIndex 0 e)
  · intro e
    simpa only [step,flow,StepFree.multiplier,StepFree.y,StepFree.z,rawMatrix,multiplier,y,z,flowX,flowA,flowB,encode_z] using h (edgeIndex 1 e)
  · intro e
    simpa only [step,flow,StepFree.multiplier,StepFree.y,StepFree.z,rawMatrix,multiplier,y,z,flowX,flowA,flowB,encode_x] using h (edgeIndex 2 e)
  · intro r e
    simpa only [step,flow,StepFree.multiplier,StepFree.y,StepFree.z,rawMatrix,multiplier,y,z,flowX,flowA,flowB,encode_a] using h (flowIndex 0 r e)
  · intro r e
    simpa only [step,flow,StepFree.multiplier,StepFree.y,StepFree.z,rawMatrix,multiplier,y,z,flowX,flowA,flowB,encode_b] using h (flowIndex 1 r e)

lemma encode_bound (c : StepFree n m) (F : FlowPoint n m) {R : ℝ}
    (hR : 0 ≤ R) (hc : c.Bounded R) (hF : F.Bounded R) : ∀i, |encode c F i| ≤ R := by
  intro i
  unfold encode
  cases h : (index n m).symm i with
  | inl ij => exact hc.1 ij.1 ij.2
  | inr w =>
    cases w with
    | inl ijk => dsimp only; split_ifs <;> first | exact hc.2.1 _ | simpa using hR
    | inr w =>
      cases w with
      | inl pe => dsimp only; split_ifs <;> first | exact hc.2.2.1 _ | exact hc.2.2.2 _ | exact hF.1 _
      | inr pre => dsimp only; split_ifs <;> first | exact hF.2.1 _ _ | exact hF.2.2 _ _

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_FiniteContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite continuation. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions Orientations
open scoped Classical MatrixOrder Matrix.Norms.Elementwise
variable {n m : ℕ}

lemma finiteStep_sound (H : MultiGraph n m) (hn : 0 < n)
    {s κ t qbar ε : ℝ} {u : Fin m → ℝ} {x : StepFree n m} {F : FlowPoint n m}
    (hε : 0 ≤ ε) (h : finiteStep H s κ t qbar ε u x F) :
    x ∈ stepFeasible H s κ t (qbar-4*ε) u := by
  refine ⟨h.1,?_⟩
  apply relaxed_flow_implies_partitions H hn (x.capacities κ u) hε
  simpa only [sub_add_cancel] using h.2

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_AffinePencil
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.RationalForms.Affine.rat_add _root_.OAI.AlgorithmicThinTrees.RationalForms.Affine.rat_smul _root_.OAI.AlgorithmicThinTrees.RationalForms.Affine.rat_sub _root_.OAI.AlgorithmicThinTrees.RationalForms.Affine.rat_sum _root_.OAI.AlgorithmicThinTrees.RationalForms.Affine.rat_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Affine pencil. -/

section

namespace AlgorithmicThinTrees.RationalForms
open Matrix Finset
open scoped BigOperators

lemma pencil_realEval {d N : ℕ} (A : Matrix (Fin N) (Fin N) (Affine d))
    (hA : A.IsSymm) (z : Fin d → ℝ) :
    (pencil A hA).realEval z=A.map (Affine.real z) := by
  ext i j
  simp only [CurrentKS.RationalSDP.Pencil.realEval,pencil,Matrix.add_apply,Matrix.map_apply,
    Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Affine.real]
  congr 1
  apply sum_congr rfl
  intro k _
  change z k * (((A i j).2 k) : ℝ) = (((A i j).2 k) : ℝ) * z k
  ring

lemma blockDiagonal_psd {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (M : J → Matrix I I ℝ) : (Matrix.blockDiagonal M).PosSemidef ↔ ∀j, (M j).PosSemidef := by
  constructor
  · intro h j
    convert h.submatrix (fun i : I => (i,j)) using 1
    all_goals try with_reducible_and_instances rfl
    ext i k
    simp [Matrix.blockDiagonal]
  · intro h
    apply PosSemidef.of_dotProduct_mulVec_nonneg
    · apply isHermitian_iff_isSymm.mpr
      apply IsSymm.ext
      intro i k
      simp only [Matrix.blockDiagonal,Matrix.of_apply]
      by_cases he : i.2=k.2
      · simp only [he,ite_true, if_true]
        exact (isHermitian_iff_isSymm.mp (h k.2).isHermitian).apply _ _
      · simp only [he,Ne.symm he,ite_false, if_false]
    · intro v
      have hn := sum_nonneg (s:=univ) (fun j _ => (h j).dotProduct_mulVec_nonneg (fun i => v (i,j)))
      change 0 ≤ ∑ j, ∑ i, v (i,j)*(∑ k, M j i k*v (k,j)) at hn
      rw [sum_comm] at hn
      simpa only [dotProduct,Matrix.mulVec,Matrix.blockDiagonal,Matrix.of_apply,Fintype.sum_prod_type,
        Pi.star_apply,star_trivial,ite_mul,zero_mul,sum_ite_eq,mem_univ,ite_true, if_true] using hn

lemma blockDiagonal_map {I J : Type*} [DecidableEq J] {d : ℕ}
    (M : J → Matrix I I (Affine d)) (z : Fin d → ℝ) :
    (Matrix.blockDiagonal M).map (Affine.real z)=Matrix.blockDiagonal (fun j => (M j).map (Affine.real z)) := by
  ext i j
  simp only [Matrix.blockDiagonal,Matrix.map_apply,Matrix.of_apply]
  split_ifs <;> simp

lemma diagonal_map {I : Type*} [DecidableEq I] {d : ℕ}
    (f : I → Affine d) (z : Fin d → ℝ) :
    (Matrix.diagonal f).map (Affine.real z)=Matrix.diagonal (fun i => Affine.real z (f i)) := by
  ext i j
  simp only [Matrix.diagonal,Matrix.map_apply,Matrix.of_apply]
  split_ifs <;> simp

lemma fromBlocks_map {I J : Type*} {d : ℕ}
    (A : Matrix I I (Affine d)) (B : Matrix J J (Affine d)) (z : Fin d → ℝ) :
    (Matrix.fromBlocks A 0 0 B).map (Affine.real z)=
      Matrix.fromBlocks (A.map (Affine.real z)) 0 0 (B.map (Affine.real z)) := by
  ext i j
  cases i <;> cases j <;> simp

lemma fromBlocks_psd {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℝ) (B : Matrix J J ℝ) :
    (Matrix.fromBlocks A 0 0 B).PosSemidef ↔ A.PosSemidef ∧ B.PosSemidef := by
  constructor
  · intro h
    exact ⟨h.submatrix Sum.inl,h.submatrix Sum.inr⟩
  · rintro ⟨ha,hb⟩
    apply PosSemidef.of_dotProduct_mulVec_nonneg
    · exact Matrix.isHermitian_fromBlocks_iff.mpr ⟨ha.isHermitian,by simp,by simp,hb.isHermitian⟩
    · intro v
      simpa only [dotProduct,Fintype.sum_sum_type,Matrix.fromBlocks_mulVec,
        Matrix.zero_mulVec,add_zero,zero_add,Sum.elim_inl,Sum.elim_inr,
        Pi.star_apply,star_trivial,Function.comp_def] using
        add_nonneg (ha.dotProduct_mulVec_nonneg (v ∘ Sum.inl))
          (hb.dotProduct_mulVec_nonneg (v ∘ Sum.inr))

lemma submatrix_equiv_psd {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℝ) (e : J ≃ I) :
    (A.submatrix e e).PosSemidef ↔ A.PosSemidef := by
  constructor
  · intro h
    have hh := h.submatrix e.symm
    have he : (A.submatrix e e).submatrix e.symm e.symm = A := by ext i j; simp
    rw [he] at hh
    exact hh
  · exact fun h => h.submatrix e

end AlgorithmicThinTrees.RationalForms
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_PencilCorrectness
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_boundQ _root_.OAI.AlgorithmicThinTrees.RationalForms.Affine.rat_add _root_.OAI.AlgorithmicThinTrees.RationalForms.Affine.rat_coord _root_.OAI.AlgorithmicThinTrees.RationalForms.Affine.rat_cst _root_.OAI.AlgorithmicThinTrees.RationalForms.Affine.rat_smul _root_.OAI.AlgorithmicThinTrees.RationalForms.Affine.rat_sub _root_.OAI.AlgorithmicThinTrees.RationalForms.Affine.rat_sum _root_.OAI.AlgorithmicThinTrees.RationalForms.Affine.rat_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation pencil correctness. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Orientations RationalForms
open scoped BigOperators
variable {n m : ℕ}

lemma real_capacityForm (κ : ℚ) (u : Fin m → ℚ) (e : Fin m) (v : Fin (dimension n m) → ℝ) :
    Affine.real v (capacityForm κ u e) = (step v).capacities (κ:ℝ) (fun e => (u e:ℝ)) e := by
  simp only [capacityForm,StepFree.capacities,step,StepFree.z,z]
  have h : (0:ℝ)<(u e:ℝ) ↔ (0:ℚ)<u e := by exact_mod_cast Iff.rfl
  simp only [h]
  split_ifs <;> simp

lemma matrixBlocks_psd (H : MultiGraph n m) (s : ℚ) (u : Fin m → ℚ)
    (v : Fin (dimension n m) → ℝ) :
    (∀b, ((matrixBlocks H s u b).map (Affine.real v)).PosSemidef) ↔
      ((step v).lowerPencil H).PosSemidef ∧ ((step v).upperPencil H).PosSemidef ∧
        ∀e, (0:ℝ)<(u e:ℝ) → ((step v).edgePencil H (s:ℝ) e).PosSemidef := by
  constructor
  · intro h
    refine ⟨?_,?_,?_⟩
    · simpa only [matrixBlocks,ite_true, if_true,real_lowerForm] using h (.inl 0)
    · simpa only [matrixBlocks,show (1 : Fin 2)≠0 from by decide,ite_false, if_false,real_upperForm] using h (.inl 1)
    · intro e he
      have he' : 0<u e := by exact_mod_cast he
      simpa only [matrixBlocks,ite_eq_left he',real_edgeForm] using h (.inr e)
  · rintro ⟨hl,hu,he⟩ b
    cases b with
    | inl p => simp only [matrixBlocks]; split_ifs <;> first | simpa only [real_lowerForm] using hl | simpa only [real_upperForm] using hu
    | inr e =>
      simp only [matrixBlocks]
      split_ifs with h
      · simpa only [real_edgeForm] using he e (by exact_mod_cast h)
      · simpa using (show (0 : Matrix (Fin n) (Fin n) ℝ).PosSemidef from PosSemidef.zero)

lemma scalarForms_nonneg (H : MultiGraph n m) (κ t qbar ε : ℚ) (u : Fin m → ℚ)
    (v : Fin (dimension n m) → ℝ) :
    (∀b, 0 ≤ Affine.real v (scalarForms H κ t qbar ε u b)) ↔
      (∀ijk, 0 ≤ (step v).multiplier ijk) ∧
      (∀e, (step v).y e ∈ Set.Icc (0:ℝ) 1) ∧
      (∀e, (step v).z e ∈ Set.Icc 0 ((κ:ℝ)+1)) ∧
      (∀e, (0:ℝ)<(u e:ℝ) → (step v).z e ≤ (κ:ℝ)+(u e:ℝ)+(t:ℝ)*(5*(step v).y e-4)) ∧
      (flow v).Feasible H ((step v).capacities (κ:ℝ) (fun e => (u e:ℝ))) (qbar:ℝ) (ε:ℝ) := by
  have cast_pos (e : Fin m) : (0:ℝ)<(u e:ℝ) ↔ (0:ℚ)<u e := by exact_mod_cast Iff.rfl
  constructor
  · intro h
    refine ⟨?_,?_,?_,?_,⟨?_,?_,?_,?_⟩⟩
    · intro ijk
      simpa only [scalarForms,ite_eq_left ijk.property,Affine.real_coord,step,StepFree.multiplier,multiplier]
        using h (.inl ijk.val)
    · intro e
      have h0 := h (.inr (.inl (0,e)))
      have h1 := h (.inr (.inl (1,e)))
      simp only [scalarForms,Matrix.cons_val_zero,Matrix.cons_val_one,Affine.real_coord,
        Affine.real_sub,Affine.real_cst,Rat.cast_one] at h0 h1
      exact ⟨h0, sub_nonneg.mp h1⟩
    · intro e
      have h2 := h (.inr (.inl (2,e)))
      have h3 := h (.inr (.inl (3,e)))
      simp [scalarForms] at h2 h3
      exact ⟨h2, h3⟩
    · intro e he
      have h4 := h (.inr (.inl (4,e)))
      simp [scalarForms,(cast_pos e).mp he] at h4
      change (step v).z e ≤ (κ:ℝ)+(u e:ℝ)+(t:ℝ)*(5*(step v).y e-4)
      change 0 ≤ (κ:ℝ)+(u e:ℝ)-(step v).z e+(t:ℝ)*(5*(step v).y e-4) at h4
      linarith only [h4]
    · intro e
      have h5 := h (.inr (.inl (5,e)))
      have h6 := h (.inr (.inl (6,e)))
      simp [scalarForms,real_capacityForm] at h5 h6
      exact ⟨h5,h6⟩
    · intro r e
      have h0 := h (.inr (.inr (.inl (0,(r,e)))))
      have h1 := h (.inr (.inr (.inl (1,(r,e)))))
      have h2 := h (.inr (.inr (.inl (2,(r,e)))))
      simp [scalarForms] at h0 h1 h2
      exact ⟨h0,h1,h2⟩
    · intro r w
      have hr := h (.inr (.inr (.inr (.inl (r,w)))))
      simp only [scalarForms,Affine.real_sub,Affine.real_cst,Affine.real_sum,Affine.real_add] at hr
      have hi (a b : Form n m) (p : Prop) [Decidable p] :
          Affine.real v (if p then a else b) = if p then Affine.real v a else Affine.real v b := by split_ifs <;> rfl
      simp only [hi,Affine.real_coord,Affine.real_zero] at hr
      have hh : ((if w=r then ε else qbar : ℚ):ℝ) = if w=r then (ε:ℝ) else (qbar:ℝ) := by split_ifs <;> rfl
      rw [hh] at hr
      exact sub_nonneg.mp hr
    · have hh := h (.inr (.inr (.inr (.inr 0))))
      simp only [scalarForms,Affine.real_sub,Affine.real_sum,Affine.real_coord,Affine.real_cst,
        Rat.cast_sub,Rat.cast_mul,Rat.cast_natCast,Rat.cast_one] at hh
      exact sub_nonneg.mp hh
  · rintro ⟨hm,hy,hz,hactive,hF⟩ b
    cases b with
    | inl ijk =>
      simp only [scalarForms]
      split_ifs with h
      · simpa only [Affine.real_coord,step_mul] using hm ⟨ijk,h⟩
      · simp
    | inr b =>
      cases b with
      | inl pe =>
        rcases pe with ⟨p,e⟩
        fin_cases p
        · simpa [scalarForms] using (hy e).1
        · simpa [scalarForms] using sub_nonneg.mpr (hy e).2
        · simpa [scalarForms] using (hz e).1
        · simpa [scalarForms] using sub_nonneg.mpr (hz e).2
        · change 0 ≤ Affine.real v (if 0<u e then Affine.cst (κ+u e)-Affine.coord (edgeIndex 1 e)+
            t • ((5:ℚ) • Affine.coord (edgeIndex 0 e)-Affine.cst 4) else 0)
          split_ifs with he
          · simp only [Affine.real_add,Affine.real_sub,Affine.real_cst,Affine.real_smul,
              Affine.real_coord,Rat.cast_add,Rat.cast_ofNat]
            have hh := hactive e ((cast_pos e).mpr he)
            change (step v).z e ≤ (κ:ℝ)+(u e:ℝ)+(t:ℝ)*(5*(step v).y e-4) at hh
            change 0 ≤ (κ:ℝ)+(u e:ℝ)-(step v).z e+(t:ℝ)*(5*(step v).y e-4)
            linarith only [hh]
          · simp
        · simpa [scalarForms] using (hF.1 e).1
        · simpa [scalarForms,real_capacityForm] using (hF.1 e).2
      | inr b =>
        cases b with
        | inl pre =>
          rcases pre with ⟨p,r,e⟩
          fin_cases p
          · simpa [scalarForms] using (hF.2.1 r e).1
          · simpa [scalarForms] using (hF.2.1 r e).2.1
          · simpa [scalarForms] using sub_nonneg.mpr (hF.2.1 r e).2.2
        | inr b =>
          cases b with
          | inl rv =>
            rcases rv with ⟨r,w⟩
            have hr := sub_nonneg.mpr (hF.2.2.1 r w)
            simp only [scalarForms,Affine.real_sub,Affine.real_sum,Affine.real_add]
            have hi (a b : Form n m) (p : Prop) [Decidable p] :
                Affine.real v (if p then a else b) = if p then Affine.real v a else Affine.real v b := by split_ifs <;> rfl
            simp only [hi,Affine.real_coord,Affine.real_zero,Affine.real_cst]
            have hh : ((if w=r then ε else qbar : ℚ):ℝ) = if w=r then (ε:ℝ) else (qbar:ℝ) := by split_ifs <;> rfl
            rw [hh]
            exact hr
          | inr p =>
            simpa only [scalarForms,Affine.real_sub,Affine.real_sum,Affine.real_coord,flow_x,
              Affine.real_cst,Rat.cast_sub,Rat.cast_mul,Rat.cast_natCast,Rat.cast_one]
              using sub_nonneg.mpr hF.2.2.2

lemma continuationPencil_psd (H : MultiGraph n m) (s κ t qbar ε : ℚ) (u : Fin m → ℚ)
    (v : Fin (dimension n m) → ℝ) :
    ((continuationPencil H s κ t qbar ε u).realEval v).PosSemidef ↔
      finiteStep H (s:ℝ) (κ:ℝ) (t:ℝ) (qbar:ℝ) (ε:ℝ) (fun e => (u e:ℝ)) (step v) (flow v) := by
  rw [continuationPencil,pencil_realEval]
  simp only [affineMatrix,←Matrix.submatrix_map,submatrix_equiv_psd,RationalForms.fromBlocks_map,
    RationalForms.blockDiagonal_map,RationalForms.diagonal_map,fromBlocks_psd,blockDiagonal_psd,Matrix.posSemidef_diagonal_iff]
  rw [matrixBlocks_psd,scalarForms_nonneg]
  simp only [finiteStep,stepCore,Set.mem_ofPred_eq,forall_and]
  tauto

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Search
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation search. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Orientations
open scoped BigOperators
variable {n m : ℕ}

lemma sizeQ_two (n m : ℕ) : 2  ≤  sizeQ n m := by
  unfold sizeQ
  linarith only [Nat.cast_nonneg (α:=ℚ) n,Nat.cast_nonneg (α:=ℚ) m]
lemma radiusQ_pos (n m : ℕ) : 0 < radiusQ n m :=
  zpow_pos (by linarith only [sizeQ_two n m]) _
lemma radiusQ_le_one (n m : ℕ) : radiusQ n m ≤ 1 := by
  exact zpow_le_one_of_nonpos₀ (by linarith only [sizeQ_two n m]) (by norm_num)

lemma boundQ_nonneg (n m : ℕ) : 0 ≤ boundQ n m := by
  unfold boundQ sizeQ
  positivity

lemma coordinate_ball (c : StepFree n m) (F : FlowPoint n m) {ρ : ℝ}
    {v : EuclideanSpace ℝ (Fin (dimension n m))}
    (hv : v ∈ Metric.closedBall (WithLp.toLp 2 (encode c F)) ρ) :
    (step v).Close c ρ ∧ (flow v).Close F ρ := by
  apply close_step_flow
  intro i
  have hh := PiLp.norm_apply_le (v-WithLp.toLp 2 (encode c F)) i
  have hd : ‖v-WithLp.toLp 2 (encode c F)‖ ≤ ρ := by
    simpa only [Metric.mem_closedBall,dist_eq_norm] using hv
  simpa only [PiLp.sub_apply,PiLp.toLp_apply,Real.norm_eq_abs] using hh.trans hd

lemma center_norm (c : StepFree n m) (F : FlowPoint n m)
    (hc : c.Bounded (6*graphSize n m)) (hF : F.Bounded (6*graphSize n m)) :
    ‖CurrentKS.RationalSDP.realVector (0 : Fin (dimension n m) → ℚ)-
      WithLp.toLp 2 (encode c F)‖ ≤ (boundQ n m:ℝ) := by
  have hb := encode_bound c F (show 0  ≤  6*graphSize n m from by positivity [graphSize_pos (n:=n) (m:=m)]) hc hF
  have hz : CurrentKS.RationalSDP.realVector (0 : Fin (dimension n m) → ℚ)=0 := by
    ext i
    simp [CurrentKS.RationalSDP.realVector]
  rw [hz,zero_sub,norm_neg,cast_boundQ]
  calc
    _  ≤  ∑i, |encode c F i| := CurrentKS.RationalSDP.norm_le_sum_abs _
    _  ≤  ∑_i : Fin (dimension n m), 6*graphSize n m := sum_le_sum (fun i _ =>  hb i)
    _ = (dimension n m:ℝ)*(6*graphSize n m) := by simp
    _  ≤  _ := by nlinarith only [graphSize_pos (n:=n) (m:=m)]

theorem search_sound (H : MultiGraph n m) (hn : 2 ≤ n) (hconn : H.Connected univ)
    (s qbar : ℚ) (β : ℝ) (u : Fin m → ℚ)
    (hs : 0 ≤ (s:ℝ)) (hsP : (s:ℝ) ≤ graphSize n m)
    (hq : (graphSize n m)^(-12:ℤ) ≤ (qbar:ℝ)) (hqm : (qbar:ℝ)+β ≤ m)
    (hβ : (graphSize n m)⁻¹/32 ≤ β) (hu : ∀e, 0 ≤ (u e:ℝ))
    {z : StepFree n m}
    (hz : z ∈ stepFeasible H (s:ℝ) (continuationBaseline m) (continuationStep m)
      ((qbar:ℝ)+β+β) (fun e =>  (u e:ℝ))) :
    (rational (search H s qbar u)).real ∈ stepFeasible H (s:ℝ)
      (continuationBaseline m) (continuationStep m) ((qbar:ℝ)-4*(errorQ n m:ℝ))
      (fun e =>  (u e:ℝ)) := by
  obtain ⟨c,F,hc,hF,hball⟩ := finite_continuation_inner_cube H hn hconn hs hsP hq hqm hβ
    (fun e =>  (u e:ℝ)) hu hz
  let B := continuationPencil H s (baselineQ m) (stepQ m) qbar (errorQ n m) u
  have hcb : Metric.closedBall (WithLp.toLp 2 (encode c F)) (radiusQ n m:ℝ) ⊆ B.feasible := by
    intro v hv
    have hclose := coordinate_ball c F hv
    rw [cast_radiusQ] at hclose
    have hf := hball (step v) (flow v) hclose.1 hclose.2
    change (B.realEval v).PosSemidef
    apply (continuationPencil_psd H s (baselineQ m) (stepQ m) qbar (errorQ n m) u v).mpr
    simpa only [cast_baselineQ,cast_stepQ,cast_errorQ] using hf
  have hsearch := B.search_accepts (radiusQ n m) (boundQ n m) 0
    (WithLp.toLp 2 (encode c F)) (radiusQ_pos n m) (radiusQ_le_one n m)
    (boundQ_nonneg n m) hcb (center_norm c F hc hF)
  have hp := (B.witness_none_iff _).mp hsearch
  change (B.realEval (fun i =>  (search H s qbar u i:ℝ))).PosSemidef at hp
  have hf := (continuationPencil_psd H s (baselineQ m) (stepQ m) qbar (errorQ n m) u _).mp hp
  rw [cast_baselineQ,cast_stepQ] at hf
  rw [rational_real]
  exact finiteStep_sound H (by omega) (by rw [cast_errorQ]; positivity [graphSize_pos (n:=n) (m:=m)]) hf

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Iteration
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation iteration. -/

section

namespace AlgorithmicThinTrees.MetricTests
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped MatrixOrder
variable {n m : ℕ}

lemma stepFeasible_mono_target (H : MultiGraph n m) (hn : 0 < n)
    {s κ t q q' : ℝ} {u : Fin m → ℝ} {x : StepFree n m}
    (hx : x ∈ stepFeasible H s κ t q u) (hqq : q' ≤ q) :
    x ∈ stepFeasible H s κ t q' u := by
  have : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  refine ⟨hx.1,fun p => (hx.2 p).trans ?_⟩
  unfold slack
  apply sub_le_sub_left
  exact mul_le_mul_of_nonneg_right hqq (by
    have hh : (1:ℝ) ≤ partCount p := by exact_mod_cast partCount_pos p
    linarith only [hh])

end AlgorithmicThinTrees.MetricTests

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped MatrixOrder
variable {n m : ℕ}

lemma search_error_le_step (H : MultiGraph n m) (hn : 2 ≤ n) (hc : H.Connected univ) :
    4*(errorQ n m:ℝ) ≤ (stepQ m:ℝ) := by
  have hP := connected_size_five H hn hc
  have hP0 := graphSize_pos (n:=n) (m:=m)
  have hpow : (128:ℝ) ≤ (graphSize n m)^9 := calc
    _ ≤ (5:ℝ)^9 := by norm_num
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) hP 9
  have hh := scaled_inverse_power hP0 1 9 hpow
  norm_num only [Nat.cast_ofNat,Nat.reduceAdd,_root_.zpow_neg_one] at hh
  have hbase := baseline_lower (n:=n) (m:=m)
  rw [cast_stepQ,cast_errorQ,continuationStep]
  linarith only [hh,hbase]

lemma cast_target (m r : ℕ) (Q g : ℚ) :
    (target m r Q g:ℝ)=(Q:ℝ)-(g:ℝ)*r*continuationStep m-2*continuationStep m := by
  simp only [target,Rat.cast_sub,Rat.cast_mul,Rat.cast_natCast,Rat.cast_ofNat,cast_stepQ]

theorem uniform_search_response_oai :
    ∃r0 : ℕ, 8 ≤ r0 ∧ ∀r : ℕ, r0 ≤ r →
      ∀(n m : ℕ) (H : MultiGraph n m), 2 ≤ n → H.Connected univ → r ≤ m →
      ∀(u : Fin m → ℚ), (∀e, 0 ≤ (u e:ℝ)) → (∀e, (u e:ℝ) ≤ 1) →
      ∀(s Q g : ℚ), 0 < (s:ℝ) → (s:ℝ) ≤ (r:ℝ)^(1/4:ℝ) →
      3*(r:ℝ)/4 ≤ (Q:ℝ) → (Q:ℝ) ≤ r →
      (r:ℝ)^(-1/8:ℝ) ≤ (g:ℝ) → (g:ℝ) ≤ 2*(r:ℝ)^(-1/8:ℝ) →
      3 ≤ (g:ℝ)*r →
      (∀p, 0 ≤ slack H.left H.right (fun e => (u e:ℝ)+continuationBaseline m) (Q:ℝ) p) →
      (rational (search H s (target m r Q g) u)).real ∈
        stepFeasible H (s:ℝ) (continuationBaseline m) (continuationStep m)
          ((Q:ℝ)-2*(g:ℝ)*r*continuationStep m) (fun e => (u e:ℝ)) := by
  obtain ⟨r0,hr0,hr⟩ := feasible_continuation_response
  refine ⟨r0,hr0,?_⟩
  intro r hrr n m H hn hc hrm u hu0 hu1 s Q g hs hsr hQ hQr hg hgg hgr hinv
  have hr8 : (8:ℝ) ≤ r := by exact_mod_cast hr0.trans hrr
  have hr1 : (1:ℝ) ≤ r := by linarith only [hr8]
  have hg0 : 0 ≤ (g:ℝ) := (Real.rpow_nonneg (Nat.cast_nonneg r) _).trans hg
  have hg2 : (g:ℝ) ≤ 2 := by
    have hp := Real.rpow_le_one_of_one_le_of_nonpos hr1 (by norm_num : (-1/8:ℝ) ≤ 0)
    linarith only [hp,hgg]
  obtain ⟨hκ,hκ1,hκm,ht,ht1,hκt,htm⟩ := continuation_parameters m
  have hsP : (s:ℝ) ≤ graphSize n m := calc
    _ ≤ (r:ℝ)^(1/4:ℝ) := hsr
    _ ≤ (r:ℝ)^((1:ℝ)) := Real.rpow_le_rpow_of_exponent_le hr1 (by norm_num)
    _ = r := Real.rpow_one _
    _ ≤ m := by exact_mod_cast hrm
    _ ≤ _ := by unfold graphSize; linarith only [Nat.cast_nonneg (α:=ℝ) n]
  have hβ : (graphSize n m)⁻¹/32 ≤ continuationStep m := by
    unfold continuationStep
    linarith only [baseline_lower (n:=n) (m:=m)]
  have hgrt : 0 ≤ (g:ℝ)*r*continuationStep m := by positivity
  have hq : (graphSize n m)^(-12:ℤ) ≤ (target m r Q g:ℝ) := by
    have hP1 : 1 ≤ graphSize n m := by linarith only [connected_size_five H hn hc]
    have hpinv : (graphSize n m)^(-12:ℤ) ≤ 1 := zpow_le_one_of_nonpos₀ hP1 (by norm_num)
    have hgt := mul_le_mul hg2 ht1 ht (by norm_num : (0:ℝ) ≤ 2)
    have hh := mul_le_mul_of_nonneg_right hgt (Nat.cast_nonneg r)
    rw [cast_target]
    nlinarith only [hpinv,hh,hr8,hQ,ht1]
  have hqm : (target m r Q g:ℝ)+continuationStep m ≤ m := by
    have hm : (r:ℝ) ≤ m := by exact_mod_cast hrm
    rw [cast_target]
    linarith only [hQr,hm,hgrt,ht]
  obtain ⟨w,hw,hp⟩ := hr r hrr n m H hn hc (fun e => (u e:ℝ)) hu0 hu1
    s Q g hs hsr hQ hQr hg hgg hinv
  obtain ⟨z,hz,_,_⟩ := response_to_stepFeasible H (by omega) ht hκt hw hp
  have hz' : z ∈ stepFeasible H (s:ℝ) (continuationBaseline m) (continuationStep m)
      ((target m r Q g:ℝ)+continuationStep m+continuationStep m) (fun e => (u e:ℝ)) := by
    rw [cast_target]
    convert hz using 1
    all_goals try with_reducible_and_instances rfl
    ring_nf
  have hout := search_sound H hn hc s (target m r Q g) (continuationStep m) u
    hs.le hsP hq hqm hβ hu0 hz'
  apply stepFeasible_mono_target H (by omega) hout
  rw [cast_target]
  have hh := mul_le_mul_of_nonneg_right hgr ht
  have he := search_error_le_step H hn hc
  rw [cast_stepQ] at he
  nlinarith only [hh,he]

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
end

theorem solution : type_of% @OAI.AlgorithmicThinTrees.MetricTests.RationalStep.uniform_search_response_oai := @OAI.AlgorithmicThinTrees.MetricTests.RationalStep.uniform_search_response_oai
