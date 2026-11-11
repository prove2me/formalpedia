-- Prove2me | solution 1 for OAI.CurrentKS.State.LightPoint.computed_candidates_progress
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:52:07.87609+00:00
-- url     : https://prove2.me/submissions/54701f00-ad5e-4ec4-9ed1-4ca1117721b3

import Mathlib
import Definitions.Def_OAIQ241TT006
import Theorems.Thm_OAI_CurrentKS_State_LightPoint_shifted_hessian_not_psd

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
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_SqSum
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalRoot
open scoped BigOperators

variable {N : ℕ}

lemma sqSum_nonneg (v : Fin N → ℚ) : 0 ≤ sqSum v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma sqSum_pos (v : Fin N → ℚ) (hv : v ≠ 0) : 0 < sqSum v := by
  have he : ∃ i,v i ≠ 0 := by
    by_contra! h
    apply hv
    funext i
    exact h i
  obtain ⟨i,hi⟩ := he
  exact Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨i,Finset.mem_univ _,sq_pos_of_ne_zero hi⟩

lemma sqSum_initialScale (v : Fin N → ℚ) :
    sqSum (initialScale v)=sqSum v/(1+sqSum v)^2 := by
  simp only [sqSum,initialScale,div_pow,Finset.sum_div]

lemma initialScale_spec (v : Fin N → ℚ) (hv : v ≠ 0) :
    0 < sqSum (initialScale v) ∧ sqSum (initialScale v) ≤ 1 := by
  have h := sqSum_pos v hv
  have hr : (0:ℚ)<1+sqSum v := by linarith
  rw [sqSum_initialScale]
  refine ⟨div_pos h (sq_pos_of_pos hr),?_⟩
  apply (div_le_one (sq_pos_of_pos hr)).mpr
  nlinarith [sq_nonneg (sqSum v)]

lemma norm_realVector (v : Fin N → ℚ) : ‖realVector v‖=Real.sqrt (sqSum v:ℝ) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp only [realVector,WithLp.ofLp_toLp,Real.norm_eq_abs,sq_abs,sqSum,Rat.cast_sum,Rat.cast_pow]

lemma realVector_div (v : Fin N → ℚ) (r : ℚ) :
    realVector (fun i => v i/r) = ((r:ℝ)⁻¹) • realVector v := by
  apply PiLp.ext
  intro i
  simp only [realVector,WithLp.ofLp_toLp,PiLp.smul_apply,smul_eq_mul,Rat.cast_div]
  ring

theorem normalize_spec (v : Fin N → ℚ) (hv : v ≠ 0) (β : ℚ) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    1-(β:ℝ) ≤ ‖realVector (normalize v β)‖ ∧ ‖realVector (normalize v β)‖ ≤ 1 ∧
    ∃ c : ℚ, 0 < c ∧ normalize v β = fun i => c*v i := by
  let u := initialScale v
  let q := sqSum u
  let U := upperSqrt q (β*q)
  have hq := initialScale_spec v hv
  have hqp : (0:ℝ)<q := by exact_mod_cast hq.1
  have hq1 : (q:ℝ)≤1 := by exact_mod_cast hq.2
  have hp : (0:ℝ)<β := by exact_mod_cast hβ
  have hp1 : (β:ℝ)≤1 := by exact_mod_cast hβ1
  have hs := upperSqrt_spec q (β*q) (mul_pos hβ hq.1) hq.1.le hq.2
  have hspos : 0 < Real.sqrt (q:ℝ) := Real.sqrt_pos.mpr hqp
  have hs1 : Real.sqrt (q:ℝ) ≤ 1 := Real.sqrt_le_one.mpr hq1
  have hql : (q:ℝ) ≤ Real.sqrt (q:ℝ) := by
    nlinarith [Real.sq_sqrt hqp.le]
  have hUpos : (0:ℝ)<U := hspos.trans_le hs.1
  have hUposQ : 0 < U := by exact_mod_cast hUpos
  have hUupper : (U:ℝ) ≤ (1+(β:ℝ))*Real.sqrt (q:ℝ) := by
    have he : ((β*q:ℚ):ℝ)=(β:ℝ)*(q:ℝ) := Rat.cast_mul ..
    rw [he] at hs
    nlinarith
  have hn : ‖realVector (normalize v β)‖=Real.sqrt (q:ℝ)/(U:ℝ) := by
    change ‖realVector (fun i => u i/U)‖=_
    rw [realVector_div,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hUpos),norm_realVector]
    ring
  rw [hn]
  refine ⟨?_,(div_le_one hUpos).mpr hs.1,?_⟩
  · apply (le_div_iff₀ hUpos).mpr
    have hu := mul_le_mul_of_nonneg_left hUupper (sub_nonneg.mpr hp1)
    nlinarith [mul_nonneg (sq_nonneg (β:ℝ)) hspos.le]
  · have hr : (0:ℚ)<1+sqSum v := by linarith [sqSum_nonneg v]
    refine ⟨((1+sqSum v)*U)⁻¹,inv_pos.mpr (mul_pos hr hUposQ),?_⟩
    funext i
    change (v i/(1+sqSum v))/U=((1+sqSum v)*U)⁻¹*v i
    simp only [div_eq_mul_inv,_root_.mul_inv_rev]
    ring
end CurrentKS.RationalRoot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_NegativeDirection
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalRoot

section
open Matrix
open scoped BigOperators

variable {N : ℕ}

lemma quadratic_scale (M : Matrix (Fin N) (Fin N) ℚ) (v : Fin N → ℚ) (c : ℚ) :
    (fun i => c*v i) ⬝ᵥ (M *ᵥ (fun i => c*v i)) = c^2*(v ⬝ᵥ (M *ᵥ v)) := by
  simp only [dotProduct,mulVec,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem negativeDirection_spec (M : Matrix (Fin N) (Fin N) ℚ) (hM : M.IsSymm)
    (β : ℚ) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    match negativeDirection M β with
    | none => (M.map (fun q : ℚ => (q:ℝ))).PosSemidef
    | some w => 1-(β:ℝ) ≤ ‖realVector w‖ ∧ ‖realVector w‖ ≤ 1 ∧ w ⬝ᵥ (M *ᵥ w) < 0 := by
  unfold negativeDirection
  cases he : KS.W17.rationalNegativeWitness N M with
  | none => exact KS.W17.rationalNegativeWitness_none_psd N M hM he
  | some v =>
    simp only [Option.map_some]
    have hv := KS.W17.rationalNegativeWitness_sound N M hM v he
    have hv0 : v ≠ 0 := by
      intro h
      simp only [h,Matrix.mulVec_zero,dotProduct_zero] at hv
      exact (lt_irrefl 0 hv)
    obtain ⟨hl,hu,c,hc,hwe⟩ := normalize_spec v hv0 β hβ hβ1
    refine ⟨hl,hu,?_⟩
    rw [hwe,quadratic_scale]
    exact mul_neg_of_pos_of_neg (sq_pos_of_pos hc) hv
end

open scoped BigOperators

variable {N : ℕ}

lemma nearest_error (t : ℚ) : |(nearest t:ℚ)-t| ≤ 1/2 := by
  unfold nearest
  split_ifs with ht
  · have hl := Int.le_ceil (t-1/2)
    have hu := Int.ceil_lt_add_one (t-1/2)
    rw [abs_le]
    constructor <;> linarith
  · have hl := Int.le_ceil (-t-1/2)
    have hu := Int.ceil_lt_add_one (-t-1/2)
    rw [Int.cast_neg,abs_le]
    constructor <;> linarith

lemma roundMesh_coord_error (ρ : ℚ) (hρ : 0 < ρ) (v : Fin N → ℚ) (i : Fin N) :
    |roundMesh ρ v i-v i| ≤ ρ/2 := by
  have he : roundMesh ρ v i-v i=ρ*((nearest (v i/ρ):ℚ)-v i/ρ) := by
    dsimp [roundMesh]
    field_simp
  rw [he,abs_mul,abs_of_pos hρ]
  exact (mul_le_mul_of_nonneg_left (nearest_error _) hρ.le).trans_eq (by ring)

lemma norm_le_sum_abs (v : EuclideanSpace ℝ (Fin N)) : ‖v‖ ≤ ∑ i,|v i| := by
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_iff.mpr
  refine ⟨Finset.sum_nonneg (fun _ _ => abs_nonneg _),?_⟩
  simpa only [Real.norm_eq_abs] using
    Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (fun i _ => abs_nonneg (v i))

lemma roundMesh_error (ρ : ℚ) (hρ : 0 < ρ) (v : Fin N → ℚ) :
    ‖realVector (roundMesh ρ v)-realVector v‖ ≤ N*(ρ:ℝ)/2 := by
  apply (norm_le_sum_abs _).trans
  calc
    (∑ i, |(realVector (roundMesh ρ v)-realVector v) i|) ≤ ∑ _ : Fin N,(ρ:ℝ)/2 := by
      apply Finset.sum_le_sum
      intro i _
      change |(roundMesh ρ v i:ℝ)-(v i:ℝ)| ≤ (ρ:ℝ)/2
      exact_mod_cast roundMesh_coord_error ρ hρ v i
    _ = N*(ρ:ℝ)/2 := by simp <;> ring

lemma realVector_scale (v : Fin N → ℚ) (c : ℚ) :
    realVector (fun i => c*v i)=(c:ℝ) • realVector v := by
  apply PiLp.ext
  intro i
  simp only [realVector,WithLp.ofLp_toLp,PiLp.smul_apply,smul_eq_mul,Rat.cast_mul]

theorem curvature_rounding (w : Fin N → ℚ) (s τ ρ : ℚ)
    (hs : 0 ≤ s) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (hρ : 0 < ρ)
    (hmesh : (N:ℚ)*ρ/2 ≤ s*τ/8) (hw : ‖realVector w‖ ≤ 1) :
    let q := roundMesh ρ (fun i => s*(1-τ)*w i)
    ‖realVector q-((s:ℝ)*(1-(τ:ℝ))) • realVector w‖ ≤ (s:ℝ)*τ/8 ∧
    ‖realVector q‖ ≤ s ∧
    ‖realVector q-(s:ℝ) • realVector w‖ ≤ 9*(s:ℝ)*τ/8 := by
  let q := roundMesh ρ (fun i => s*(1-τ)*w i)
  have hs' : (0:ℝ) ≤ s := by exact_mod_cast hs
  have ht' : (0:ℝ) ≤ τ := by exact_mod_cast hτ
  have ht1' : (τ:ℝ) ≤ 1 := by exact_mod_cast hτ1
  have hm : (N:ℝ)*(ρ:ℝ)/2 ≤ (s:ℝ)*τ/8 := by exact_mod_cast hmesh
  have he := (roundMesh_error ρ hρ (fun i => s*(1-τ)*w i)).trans hm
  rw [realVector_scale] at he
  push_cast at he
  have ht : ‖((s:ℝ)*(1-(τ:ℝ))) • realVector w‖ ≤ (s:ℝ)*(1-(τ:ℝ)) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hs' (sub_nonneg.mpr ht1'))]
    exact mul_le_of_le_one_right (mul_nonneg hs' (sub_nonneg.mpr ht1')) hw
  have hqn : ‖realVector q‖ ≤ s := by
    have hb := norm_le_norm_sub_add (realVector q) (((s:ℝ)*(1-(τ:ℝ))) • realVector w)
    nlinarith [mul_nonneg hs' ht']
  refine ⟨he,hqn,?_⟩
  have hd : ‖((s:ℝ)*(1-(τ:ℝ))) • realVector w-(s:ℝ) • realVector w‖ ≤ (s:ℝ)*τ := by
    rw [← sub_smul,norm_smul,Real.norm_eq_abs]
    have hx : (s:ℝ)*(1-(τ:ℝ))-(s:ℝ) = -((s:ℝ)*τ) := by ring
    rw [hx,abs_neg,abs_of_nonneg (mul_nonneg hs' ht')]
    exact mul_le_of_le_one_right (mul_nonneg hs' ht') hw
  have hb := norm_sub_le_norm_sub_add_norm_sub (realVector q) (((s:ℝ)*(1-(τ:ℝ))) • realVector w) ((s:ℝ) • realVector w)
  linarith
end CurrentKS.RationalRoot

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

lemma select_le (score : α → ℚ) (a : α) (l : List α) :
    ∀ b ∈ a :: l, score (select score a l) ≤ score b := by
  induction l generalizing a with
  | nil => simp [select]
  | cons b bs ih =>
    rw [select]
    split
    · rename_i h
      intro c hc
      have hb := ih b b (by simp)
      simp only [List.mem_cons] at hc
      rcases hc with rfl | rfl | hc
      · exact hb.trans h.le
      · exact hb
      · exact ih b c (by simp [hc])
    · rename_i h
      intro c hc
      have ha := ih a a (by simp)
      simp only [List.mem_cons] at hc
      rcases hc with rfl | rfl | hc
      · exact ha
      · exact ha.trans (le_of_not_gt h)
      · exact ih a c (by simp [hc])

end CurrentKS.Descent

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_QuadraticDifferenceBound
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Difference
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma quadratic_difference_bound (B : E →L[ℝ] E →L[ℝ] ℝ) (q r : E) :
    |B q q-B r r| ≤ ‖B‖*‖q-r‖*(‖q‖+‖r‖) := by
  have he : B q q-B r r = B (q-r) q+B r (q-r) := by
    simp only [map_sub,_root_.sub_apply]
    ring
  rw [he]
  apply (abs_add_le _ _).trans
  have h1 : |B (q-r) q| ≤ ‖B‖*‖q-r‖*‖q‖ :=
    (B.le_opNorm₂ _ _)
  have h2 : |B r (q-r)| ≤ ‖B‖*‖r‖*‖q-r‖ :=
    (B.le_opNorm₂ _ _)
  nlinarith

theorem rounded_negative_curvature (B : E →L[ℝ] E →L[ℝ] ℝ) (q w : E)
    {a M s : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hM : 1 ≤ M) (hs : 0 ≤ s)
    (hBn : ‖B‖ ≤ M) (hwn : ‖w‖ ≤ 1) (hwl : 1-a/(4096*M) ≤ ‖w‖)
    (hcurv : B w w ≤ -(111/16:ℝ)*a*‖w‖^2)
    (hqn : ‖q‖ ≤ s) (hqw : ‖q-s • w‖ ≤ 9*s*(a/(1024*M))/8) :
    B q q ≤ -6*a*s^2 := by
  have hMp : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hβ : a/(4096*M) ≤ (1/4096:ℝ) := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<4096*M)).mpr
    calc
      a ≤ 1 := ha1
      _ ≤ (1/4096:ℝ)*(4096*M) := by nlinarith
  have hwl' : (4095/4096:ℝ) ≤ ‖w‖ := by linarith
  have hws : (4095/4096:ℝ)^2 ≤ ‖w‖^2 :=
    pow_le_pow_left₀ (by norm_num) hwl' 2
  have hrn : ‖s • w‖ ≤ s := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs]
    nlinarith
  have hd := quadratic_difference_bound B q (s • w)
  have her : |B q q-B (s • w) (s • w)| ≤ (9/4096:ℝ)*a*s^2 := by
    apply hd.trans
    calc
      ‖B‖*‖q-s • w‖*(‖q‖+‖s • w‖) ≤
          M*(9*s*(a/(1024*M))/8)*(s+s) := by
        apply mul_le_mul
        · exact mul_le_mul hBn hqw (norm_nonneg _) (le_of_lt hMp)
        · exact add_le_add hqn hrn
        · positivity
        · positivity
      _ = (9/4096:ℝ)*a*s^2 := by field_simp <;> ring
  have hsB : B (s • w) (s • w)=s^2*B w w := by
    simp only [map_smul,_root_.smul_apply,smul_eq_mul]
    ring
  rw [hsB] at her
  have hu := (abs_le.mp her).2
  have hc := mul_le_mul_of_nonneg_left hcurv (sq_nonneg s)
  have he := mul_le_mul_of_nonneg_left hws (show 0 ≤ (111/16:ℝ)*a*s^2 by positivity)
  nlinarith

end CurrentKS.Difference

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_ShiftedHessian
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalRoot
open Matrix CurrentKS.Difference
open scoped BigOperators

variable {N : ℕ}

lemma shiftedHessian_symm (H : Matrix (Fin N) (Fin N) ℚ) (hH : H.IsSymm) (a : ℚ) :
    (shiftedHessian H a).IsSymm := by
  exact hH.add (isSymm_one.smul _)

lemma realQuadratic_cast (H : Matrix (Fin N) (Fin N) ℚ) (v : Fin N → ℚ) :
    realQuadratic H (realVector v) = ((v ⬝ᵥ (H *ᵥ v):ℚ):ℝ) := by
  simp only [realQuadratic,realVector,WithLp.ofLp_toLp,dotProduct,mulVec,
    Rat.cast_sum,Rat.cast_mul,Matrix.map_apply]

lemma realQuadratic_shift (H : Matrix (Fin N) (Fin N) ℚ) (a : ℚ)
    (u : EuclideanSpace ℝ (Fin N)) :
    realQuadratic (shiftedHessian H a) u=realQuadratic H u+7*(a:ℝ)*‖u‖^2 := by
  have he : (shiftedHessian H a).map (fun t : ℚ => (t:ℝ)) =
      H.map (fun t : ℚ => (t:ℝ))+(7*(a:ℝ)) • 1 := by
    ext i j
    by_cases hi : i=j <;> simp [shiftedHessian,hi]
  rw [realQuadratic,he,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    dotProduct_add,dotProduct_smul]
  congr 1
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [dotProduct,pow_two,smul_eq_mul]

lemma curvature_parameters {a M : ℚ} (ha : 0 < a) (ha1 : a ≤ 1) (hM : 1 ≤ M) :
    0 < a/(4096*M) ∧ a/(4096*M)≤1 ∧ 0 ≤ a/(1024*M) ∧ a/(1024*M)≤1 := by
  have hMp : 0 < M := lt_of_lt_of_le zero_lt_one hM
  refine ⟨by positivity,?_,by positivity,?_⟩
  · apply (div_le_one (by positivity : (0:ℚ)<4096*M)).mpr
    linarith
  · apply (div_le_one (by positivity : (0:ℚ)<1024*M)).mpr
    linarith

theorem computedCurvature_spec (H : Matrix (Fin N) (Fin N) ℚ) (hH : H.IsSymm)
    (B : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
    (a M s ρ : ℚ) (ha : 0 < a) (ha1 : a ≤ 1) (hM : 1 ≤ M) (hs : 0 ≤ s) (hρ : 0 < ρ)
    (hmesh : (N:ℚ)*ρ/2 ≤ s*(a/(1024*M))/8) (hBn : ‖B‖ ≤ (M:ℝ))
    (herr : ∀ u,|realQuadratic H u-B u u| ≤ (a:ℝ)/16*‖u‖^2) :
    match computedCurvature H a M s ρ with
    | none => ∀ u,0 ≤ realQuadratic H u+7*(a:ℝ)*‖u‖^2
    | some q => ‖realVector q‖ ≤ (s:ℝ) ∧ B (realVector q) (realVector q) ≤ -6*(a:ℝ)*(s:ℝ)^2 := by
  have hpar := curvature_parameters ha ha1 hM
  have hd := negativeDirection_spec (shiftedHessian H a) (shiftedHessian_symm H hH a)
    (a/(4096*M)) hpar.1 hpar.2.1
  unfold computedCurvature
  cases he : negativeDirection (shiftedHessian H a) (a/(4096*M)) with
  | none =>
    simp only [he] at hd
    simp only [Option.map_none]
    intro u
    rw [← realQuadratic_shift]
    exact hd.dotProduct_mulVec_nonneg u
  | some w =>
    simp only [he] at hd
    simp only [Option.map_some]
    have hb : B (realVector w) (realVector w) ≤ -(111/16:ℝ)*(a:ℝ)*‖realVector w‖^2 := by
      have hn : realQuadratic (shiftedHessian H a) (realVector w)<0 := by
        rw [realQuadratic_cast]
        exact_mod_cast hd.2.2
      rw [realQuadratic_shift] at hn
      have herrw := (abs_le.mp (herr (realVector w))).1
      linarith
    have hr := curvature_rounding w s (a/(1024*M)) ρ hs hpar.2.2.1 hpar.2.2.2 hρ hmesh hd.2.1
    refine ⟨hr.2.1,?_⟩
    have hl : 1-(a:ℝ)/(4096*(M:ℝ)) ≤ ‖realVector w‖ := by
      simpa only [Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat] using hd.1
    have hq : ‖realVector (roundMesh ρ (fun i => s*(1-a/(1024*M))*w i))-
        (s:ℝ) • realVector w‖ ≤ 9*(s:ℝ)*((a:ℝ)/(1024*(M:ℝ)))/8 := by
      simpa only [Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat] using hr.2.2
    exact rounded_negative_curvature B _ (realVector w) (a:=(a:ℝ)) (M:=(M:ℝ))
      (s:=(s:ℝ)) (by exact_mod_cast ha) (by exact_mod_cast ha1) (by exact_mod_cast hM)
      (by exact_mod_cast hs) hBn hd.2.1 hl hb hr.2.1 hq

end CurrentKS.RationalRoot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_DerivLine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Difference

section
open Filter
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma deriv_line {f : E → ℝ} {x h : E} {t : ℝ}
    (hf : DifferentiableAt ℝ f (x+t • h)) :
    deriv (fun s : ℝ => f (x+s • h)) t = fderiv ℝ f (x+t • h) h := by
  have hh : HasDerivAt (fun s : ℝ => x+s • h) h t := by
    have hh := ((hasDerivAt_id t).smul_const h).const_add x
    simp only [one_smul] at hh
    exact hh
  exact (hf.hasFDerivAt.comp_hasDerivAt t hh).deriv

lemma deriv_line_eventually {f : E → ℝ} {x h : E} {t : ℝ}
    (hf : ContDiffAt ℝ 2 f (x+t • h)) :
    deriv (fun s : ℝ => f (x+s • h)) =ᶠ[𝓝 t]
      (fun s => fderiv ℝ f (x+s • h) h) := by
  have hh : HasDerivAt (fun s : ℝ => x+s • h) h t := by
    have hh := ((hasDerivAt_id t).smul_const h).const_add x
    simp only [one_smul] at hh
    exact hh
  have he : ∀ᶠ s in 𝓝 t, ContDiffAt ℝ 2 f (x+s • h) :=
    (hf.eventually (by norm_num)).filter_mono hh.continuousAt
  filter_upwards [he] with s hs
  exact deriv_line (hs.differentiableAt (by norm_num))

lemma deriv_fderiv_line {f : E → ℝ} {x h : E} {t : ℝ}
    (hf : ContDiffAt ℝ 2 f (x+t • h)) :
    deriv (fun s : ℝ => fderiv ℝ f (x+s • h) h) t =
      fderiv ℝ (fderiv ℝ f) (x+t • h) h h := by
  have hh : HasDerivAt (fun s : ℝ => x+s • h) h t := by
    have hh := ((hasDerivAt_id t).smul_const h).const_add x
    simp only [one_smul] at hh
    exact hh
  have hfdc : ContDiffAt ℝ 1 (fderiv ℝ f) (x+t • h) :=
    hf.fderiv_right (by norm_num)
  have hfd : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) (x+t • h)) (x+t • h) :=
    (hfdc.differentiableAt (by norm_num)).hasFDerivAt
  have hc : HasDerivAt (fun s : ℝ => fderiv ℝ f (x+s • h))
      (fderiv ℝ (fderiv ℝ f) (x+t • h) h) t := hfd.comp_hasDerivAt t hh
  have hd : HasDerivAt (fun s : ℝ => fderiv ℝ f (x+s • h) h)
      (fderiv ℝ (fderiv ℝ f) (x+t • h) h h+fderiv ℝ f (x+t • h) 0) t :=
    hc.clm_apply (hasDerivAt_const t h)
  simpa only [map_zero,add_zero] using hd.deriv

lemma second_deriv_line {f : E → ℝ} {x h : E} {t : ℝ}
    (hf : ContDiffAt ℝ 2 f (x+t • h)) :
    deriv (deriv (fun s : ℝ => f (x+s • h))) t =
      fderiv ℝ (fderiv ℝ f) (x+t • h) h h := by
  exact (deriv_line_eventually hf).deriv_eq.trans (deriv_fderiv_line hf)

end

open scoped BigOperators

end CurrentKS.Difference

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_QuadraticRemainder
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Difference
open Set
open scoped ContDiff

theorem quadratic_remainder {f : ℝ → ℝ} {h M : ℝ} (hh : 0 < h)
    (hf : ContDiffOn ℝ 3 f (Icc 0 h)) (hf0 : ContDiffAt ℝ 3 f 0)
    (hM : ∀ t ∈ Ioo 0 h, |iteratedDeriv 3 f t| ≤ M) :
    |f h - (f 0 + h * iteratedDeriv 1 f 0 + h^2/2 * iteratedDeriv 2 f 0)| ≤ M*h^3/6 := by
  obtain ⟨t,ht,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n:=2) (ne_of_lt hh)
    (by norm_num only [Nat.cast_ofNat, Set.uIcc_of_le hh.le]; exact hf)
  simp only [Set.uIoo_of_le hh.le, Set.uIcc_of_le hh.le] at ht he
  have h1 := iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hh)
    (hf0.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)) (left_mem_Icc.mpr hh.le)
  have h2 := iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hh)
    (hf0.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)) (left_mem_Icc.mpr hh.le)
  have heval : taylorWithinEval f 2 (Icc 0 h) 0 h =
      f 0 + h * iteratedDeriv 1 f 0 + h^2/2 * iteratedDeriv 2 f 0 := by
    rw [show 2=1+1 from rfl,taylorWithinEval_succ,taylorWithinEval_succ,
      taylor_within_zero_eval]
    norm_num only [Nat.reduceAdd, Nat.factorial, Nat.cast_ofNat, zero_add, one_mul, inv_one,sub_zero,pow_one,smul_eq_mul]
    rw [h1,h2]
    ring
  rw [heval] at he
  rw [he]
  norm_num only [Nat.factorial, Nat.cast_ofNat, sub_zero, abs_div, abs_mul,
    abs_pow, abs_of_pos hh]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hM t ht) (by positivity)) (by norm_num)

theorem gradient_error {fp fm f0 g H h M e vp vm : ℝ}
    (hh : 0 < h) (_he : 0 ≤ e)
    (hp : |fp-(f0+h*g+h^2/2*H)| ≤ M*h^3/6)
    (hm : |fm-(f0-h*g+h^2/2*H)| ≤ M*h^3/6)
    (hvp : |vp-fp| ≤ e) (hvm : |vm-fm| ≤ e) :
    |(vp-vm)/(2*h)-g| ≤ M*h^2/6+e/h := by
  have ha : |(vp-vm)-2*h*g| ≤ M*h^3/3+2*e := by
    have H1 := abs_add_le (vp-fp) (fp-(f0+h*g+h^2/2*H))
    have H2 := abs_add_le ((vp-fp)+(fp-(f0+h*g+h^2/2*H)))
      (-(vm-fm)-(fm-(f0-h*g+h^2/2*H)))
    have H3 := abs_sub (-(vm-fm)) (fm-(f0-h*g+h^2/2*H))
    rw [abs_neg] at H3
    have : (vp-fp)+(fp-(f0+h*g+h^2/2*H))+
        (-(vm-fm)-(fm-(f0-h*g+h^2/2*H))) = (vp-vm)-2*h*g := by ring
    rw [this] at H2
    linarith
  have heq : (vp-vm)/(2*h)-g = ((vp-vm)-2*h*g)/(2*h) := by field_simp
  rw [heq,abs_div,abs_of_pos (mul_pos (by norm_num) hh)]
  apply (div_le_iff₀ (mul_pos (by norm_num) hh)).mpr
  calc
    |vp-vm-2*h*g| ≤ M*h^3/3+2*e := ha
    _ = (M*h^2/6+e/h)*(2*h) := by field_simp <;> ring

theorem diagonal_error {fp fm f0 g H h M e vp vm v0 : ℝ}
    (hh : 0 < h) (_he : 0 ≤ e)
    (hp : |fp-(f0+h*g+h^2/2*H)| ≤ M*h^3/6)
    (hm : |fm-(f0-h*g+h^2/2*H)| ≤ M*h^3/6)
    (hvp : |vp-fp| ≤ e) (hvm : |vm-fm| ≤ e) (hv0 : |v0-f0| ≤ e) :
    |(vp-2*v0+vm)/h^2-H| ≤ M*h/3+4*e/h^2 := by
  have hp' := abs_le.mp hp
  have hm' := abs_le.mp hm
  have hvp' := abs_le.mp hvp
  have hvm' := abs_le.mp hvm
  have hv0' := abs_le.mp hv0
  have ha : |vp-2*v0+vm-h^2*H| ≤ M*h^3/3+4*e := by
    rw [abs_le]
    constructor <;> linarith
  have heq : (vp-2*v0+vm)/h^2-H = (vp-2*v0+vm-h^2*H)/h^2 := by field_simp
  rw [heq,abs_div,abs_of_pos (sq_pos_of_pos hh)]
  apply (div_le_iff₀ (sq_pos_of_pos hh)).mpr
  calc
    |vp-2*v0+vm-h^2*H| ≤ M*h^3/3+4*e := ha
    _ = (M*h/3+4*e/h^2)*h^2 := by field_simp

end CurrentKS.Difference

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_LineShiftIteratedDeriv
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Difference

section
open Set
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma line_shift_iteratedDeriv (f : E → ℝ) (x v : E) (n : ℕ) (t : ℝ) :
    iteratedDeriv n (fun r : ℝ => f ((x+t • v)+r • v)) 0 =
      iteratedDeriv n (fun r : ℝ => f (x+r • v)) t := by
  have he : (fun r : ℝ => f ((x+t • v)+r • v)) =
      (fun r : ℝ => (fun s : ℝ => f (x+s • v)) (t+r)) := by
    funext r
    dsimp only
    rw [add_smul,add_assoc]
  rw [he]
  simpa only [add_zero] using congrFun (iteratedDeriv_comp_const_add n (fun s : ℝ => f (x+s • v)) t) 0

theorem line_quadratic_remainder {f : E → ℝ} {x v : E} {s M : ℝ}
    (hs : 0 < s)
    (hf : ∀ t ∈ Icc 0 s,ContDiffAt ℝ 3 f (x+t • v))
    (hM : ∀ t ∈ Ioo 0 s,
      |iteratedDeriv 3 (fun r : ℝ => f ((x+t • v)+r • v)) 0| ≤ M) :
    |f (x+s • v)-(f x+s*(fderiv ℝ f x v)+
      s^2/2*(fderiv ℝ (fderiv ℝ f) x v v))| ≤ M*s^3/6 := by
  have hline : ContDiff ℝ 3 (fun t : ℝ => x+t • v) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hc : ∀ t ∈ Icc 0 s,ContDiffAt ℝ 3 (fun r : ℝ => f (x+r • v)) t := by
    intro t ht
    exact (hf t ht).comp t hline.contDiffAt
  have h0 := hc 0 (left_mem_Icc.mpr hs.le)
  have h2 : ContDiffAt ℝ 2 f (x+(0:ℝ) • v) :=
    (hf 0 (left_mem_Icc.mpr hs.le)).of_le (by norm_num)
  have hd1 := deriv_line (h2.differentiableAt (by norm_num))
  have hd2 := second_deriv_line h2
  have hbound : ∀ t ∈ Ioo 0 s,
      |iteratedDeriv 3 (fun r : ℝ => f (x+r • v)) t| ≤ M := by
    intro t ht
    simpa only [line_shift_iteratedDeriv] using hM t ht
  have ht := quadratic_remainder hs (fun t ht => (hc t ht).contDiffWithinAt) h0 hbound
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero,hd1,hd2,zero_smul,add_zero] using ht

end

open Set
open scoped ContDiff

lemma linear_remainder {f : ℝ → ℝ} {s M : ℝ} (hs : 0 < s)
    (hf : ContDiffOn ℝ 2 f (Icc 0 s)) (hf0 : ContDiffAt ℝ 2 f 0)
    (hM : ∀ t ∈ Ioo 0 s,|iteratedDeriv 2 f t| ≤ M) :
    |f s-(f 0+s*deriv f 0)| ≤ M*s^2/2 := by
  obtain ⟨t,ht,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n:=1) (ne_of_lt hs)
    (by norm_num only [Nat.cast_ofNat, Set.uIcc_of_le hs.le]; exact hf)
  simp only [Set.uIoo_of_le hs.le, Set.uIcc_of_le hs.le] at ht he
  have h1 := iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hs)
    (hf0.of_le (by norm_num : (1:WithTop ℕ∞) ≤ 2)) (left_mem_Icc.mpr hs.le)
  have hformula : taylorWithinEval f 1 (Icc 0 s) 0 s=f 0+s*deriv f 0 := by
    rw [show 1=0+1 from rfl,taylorWithinEval_succ,taylor_within_zero_eval]
    norm_num only [Nat.factorial,Nat.cast_one,inv_one,sub_zero,pow_one,smul_eq_mul,one_mul]
    rw [h1,iteratedDeriv_one]
  rw [hformula] at he
  rw [he]
  norm_num only [Nat.factorial,Nat.cast_ofNat,sub_zero,abs_div,abs_mul,abs_pow,
    abs_of_pos hs]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hM t ht) (by positivity)) (by norm_num)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma line_linear_remainder {f : E → ℝ} {x v : E} {s M : ℝ} (hs : 0 < s)
    (hf : ∀ t ∈ Icc 0 s,ContDiffAt ℝ 2 f (x+t • v))
    (hM : ∀ t ∈ Ioo 0 s,|iteratedDeriv 2 (fun r : ℝ => f ((x+t • v)+r • v)) 0| ≤ M) :
    |f (x+s • v)-(f x+s*(fderiv ℝ f x v))| ≤ M*s^2/2 := by
  have hline : ContDiff ℝ 2 (fun t : ℝ => x+t • v) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hc : ∀ t ∈ Icc 0 s,ContDiffAt ℝ 2 (fun r : ℝ => f (x+r • v)) t := by
    intro t ht
    exact (hf t ht).comp t hline.contDiffAt
  have h0 := hc 0 (left_mem_Icc.mpr hs.le)
  have hd := deriv_line ((hf 0 (left_mem_Icc.mpr hs.le)).differentiableAt (by norm_num))
  have hb : ∀ t ∈ Ioo 0 s,|iteratedDeriv 2 (fun r : ℝ => f (x+r • v)) t| ≤ M := by
    intro t ht
    simpa only [line_shift_iteratedDeriv] using hM t ht
  have hh := linear_remainder hs (fun t ht => (hc t ht).contDiffWithinAt) h0 hb
  simpa only [hd,zero_smul,add_zero] using hh

end CurrentKS.Difference

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_ChooseCoordinate
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Difference

section
open scoped BigOperators

lemma chooseCoordinate_max {N : ℕ} [NeZero N] (g : Fin N → ℚ) (i : Fin N) :
    |g i| ≤ |g (chooseCoordinate g)| := by
  have hh := CurrentKS.Descent.select_le (fun i => -|g i|) (0 : Fin N) (List.finRange N)
    i (by simp)
  exact neg_le_neg_iff.mp hh

theorem chosen_gradient {N : ℕ} [NeZero N] (g : Fin N → ℝ) (ghat : Fin N → ℚ)
    {a : ℝ} (ha : 0 < a) (herr : ∀ i,|(ghat i:ℝ)-g i| ≤ a/8)
    (hlarge : ∃ i,a ≤ |g i|) :
    let i := chooseCoordinate ghat
    3*a/4 ≤ |g i| ∧ ((0 ≤ ghat i → 0 < g i) ∧ (ghat i < 0 → g i < 0)) := by
  dsimp
  obtain ⟨j,hj⟩ := hlarge
  let i := chooseCoordinate ghat
  have hm : |(ghat j:ℝ)| ≤ |(ghat i:ℝ)| := by exact_mod_cast chooseCoordinate_max ghat j
  have hjerr := abs_le.mp (herr j)
  have hierr := abs_le.mp (herr i)
  have hsmall : |g j|-a/8 ≤ |(ghat j:ℝ)| := by
    have hh := abs_sub_abs_le_abs_sub (g j) (ghat j:ℝ)
    rw [abs_sub_comm] at hh
    linarith [herr j]
  have hgsize : 3*a/4 ≤ |g i| := by
    have hh := abs_sub_abs_le_abs_sub (ghat i:ℝ) (g i)
    linarith [herr i]
  refine ⟨hgsize,?_,?_⟩
  · intro hnonneg
    have hn : (0:ℝ) ≤ ghat i := by exact_mod_cast hnonneg
    rw [abs_of_nonneg hn] at hm
    linarith
  · intro hneg
    have hn : (ghat i:ℝ) < 0 := by exact_mod_cast hneg
    rw [abs_of_neg hn] at hm
    linarith

lemma gradient_decrease {f0 f1 a s M v : ℝ} (ha : 0 < a) (hs : 0 < s)
    (hs1 : s ≤ 1/4) (hstep : M*s ≤ a/4) (hv : v ≤ -3*a/4)
    (htaylor : f1 ≤ f0+s*v+M*s^2/2) : f1 ≤ f0-(5/2:ℝ)*a*s^2 := by
  have hv' := mul_le_mul_of_nonneg_left hv hs.le
  have hstep' := mul_le_mul_of_nonneg_left hstep hs.le
  have hsmall := mul_le_mul_of_nonneg_left hs1 (show 0≤a*s by positivity)
  nlinarith

lemma opposite_decrease {f0 fp fm L Q a s M : ℝ} (ha : 0 < a) (hs : 0 < s)
    (hstep : M*s ≤ a/4) (hQ : Q ≤ -6*a*s^2)
    (hp : fp ≤ f0+L+Q/2+M*s^3/6) (hm : fm ≤ f0-L+Q/2+M*s^3/6) :
    fp ≤ f0-2*a*s^2 ∨ fm ≤ f0-2*a*s^2 := by
  have he := mul_le_mul_of_nonneg_left hstep (sq_nonneg s)
  have hpos : 0<a*s^2 := by positivity
  by_contra h
  push Not at h
  nlinarith

end

open Set
open scoped ContDiff

variable {N : ℕ}

lemma rationalGradientDirection_cast [NeZero N] (g : Fin N → ℚ) :
    (fun i => (rationalGradientDirection g i:ℝ))=gradientDirection g := by
  classical
  funext j
  simp only [rationalGradientDirection,gradientDirection,Pi.smul_apply,smul_eq_mul,
    Rat.cast_mul,Pi.single_apply]
  split_ifs <;> norm_num

lemma gradientDirection_bound [NeZero N] (g : Fin N → ℚ) : ‖gradientDirection g‖ ≤ 1 := by
  classical
  unfold gradientDirection
  split_ifs <;> simp only [neg_smul,one_smul,norm_neg]
  all_goals
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    by_cases hi : i=chooseCoordinate g <;> simp [hi]

lemma gradientDirection_derivative [NeZero N] (L : (Fin N → ℝ) →L[ℝ] ℝ)
    (ghat : Fin N → ℚ) {a : ℝ} (ha : 0 < a)
    (herr : ∀ i,|(ghat i:ℝ)-L (Pi.single i (1:ℝ))| ≤ a/8)
    (hlarge : ∃ i,a ≤ |L (Pi.single i (1:ℝ))|) :
    L (gradientDirection ghat) ≤ -3*a/4 := by
  have hc := chosen_gradient (fun i => L (Pi.single i (1:ℝ))) ghat ha herr hlarge
  dsimp only at hc
  unfold gradientDirection
  split_ifs with hs
  · have hp := hc.2.1 hs
    rw [abs_of_pos hp] at hc
    simp only [map_smul,smul_eq_mul,neg_one_mul]
    linarith [hc.1]
  · have hp := hc.2.2 (lt_of_not_ge hs)
    rw [abs_of_neg hp] at hc
    simp only [one_smul]
    linarith [hc.1]

theorem gradient_candidate_decrease [NeZero N] (f : (Fin N → ℝ) → ℝ)
    (x : Fin N → ℝ) (ghat : Fin N → ℚ) {a s M : ℝ}
    (ha : 0 < a) (hs : 0 < s) (hs1 : s ≤ 1/4) (hstep : M*s ≤ a/4)
    (herr : ∀ i,|(ghat i:ℝ)-fderiv ℝ f x (Pi.single i (1:ℝ))| ≤ a/8)
    (hlarge : ∃ i,a ≤ |fderiv ℝ f x (Pi.single i (1:ℝ))|)
    (hf : ∀ t ∈ Icc 0 s,ContDiffAt ℝ 2 f (x+t • gradientDirection ghat))
    (hM : ∀ t ∈ Ioo 0 s,
      |iteratedDeriv 2 (fun r : ℝ => f ((x+t • gradientDirection ghat)+r • gradientDirection ghat)) 0| ≤ M) :
    f (x+s • gradientDirection ghat) ≤ f x-(5/2:ℝ)*a*s^2 := by
  have hd := gradientDirection_derivative (fderiv ℝ f x) ghat ha herr hlarge
  have ht := (abs_le.mp (line_linear_remainder hs hf hM)).2
  apply gradient_decrease ha hs hs1 hstep hd
  linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem opposite_candidates_decrease (f : E → ℝ) (x q : E) {a s M : ℝ}
    (ha : 0 < a) (hs : 0 < s) (hstep : M*s ≤ a/4)
    (hQ : fderiv ℝ (fderiv ℝ f) x q q ≤ -6*a*s^2)
    (hf : ∀ v ∈ ({q,-q}:Set E),∀ t ∈ Icc (0:ℝ) 1,ContDiffAt ℝ 3 f (x+t • v))
    (hM : ∀ v ∈ ({q,-q}:Set E),∀ t ∈ Ioo (0:ℝ) 1,
      |iteratedDeriv 3 (fun r : ℝ => f ((x+t • v)+r • v)) 0| ≤ M*s^3) :
    f (x+q) ≤ f x-2*a*s^2 ∨ f (x-q) ≤ f x-2*a*s^2 := by
  have hp := line_quadratic_remainder (by norm_num : (0:ℝ)<1)
    (hf q (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (hM q (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have hm := line_quadratic_remainder (by norm_num : (0:ℝ)<1)
    (hf (-q) (by simp)) (hM (-q) (by simp))
  simp only [one_smul,one_mul,one_pow] at hp hm
  have hneg : fderiv ℝ (fderiv ℝ f) x (-q) (-q)=fderiv ℝ (fderiv ℝ f) x q q := by
    simp only [map_neg,_root_.neg_apply,neg_neg]
  rw [hneg,map_neg,← sub_eq_add_neg] at hm
  apply opposite_decrease (L := fderiv ℝ f x q) ha hs hstep hQ
  · linarith [(abs_le.mp hp).2]
  · linarith [(abs_le.mp hm).2]

end CurrentKS.Difference

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_IteratedDerivCompScale
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Difference

section

lemma iteratedDeriv_comp_scale (n : ℕ) (f : ℝ → ℝ) (a c : ℝ) :
    iteratedDeriv n (fun x => f (c*x)) a = c^n*iteratedDeriv n f (c*a) := by
  induction n generalizing a with
  | zero => simp only [iteratedDeriv_zero,pow_zero,one_mul]
  | succ n ih =>
    have he : iteratedDeriv n (fun x => f (c*x)) = fun x => c^n*iteratedDeriv n f (c*x) := funext ih
    rw [iteratedDeriv_succ,iteratedDeriv_succ,he]
    rw [show (fun x => c^n*iteratedDeriv n f (c*x)) =
      (fun x => (fun y => c^n*iteratedDeriv n f y) (c*x)) from rfl]
    rw [deriv_comp_mul_left c (fun y => c^n*iteratedDeriv n f y) a,deriv_const_mul_field,smul_eq_mul,pow_succ]
    ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma line_derivative_scale (n : ℕ) (f : E → ℝ) (x h : E) (c : ℝ) :
    iteratedDeriv n (fun t : ℝ => f (x+t • (c • h))) 0 =
      c^n*iteratedDeriv n (fun t : ℝ => f (x+t • h)) 0 := by
  have he : (fun t : ℝ => f (x+t • (c • h))) =
      (fun t : ℝ => (fun r : ℝ => f (x+r • h)) (c*t)) := by
    ext t
    rw [smul_smul,mul_comm]
  rw [he,iteratedDeriv_comp_scale n (fun r : ℝ => f (x+r • h)) 0 c,mul_zero]

lemma bounded_directional_derivative (n : ℕ) (f : E → ℝ) (x h : E) {s M : ℝ}
    (hs : 0 < s) (hh : ‖h‖ ≤ s)
    (hM : ∀ u : E, ‖u‖ ≤ 1 → |iteratedDeriv n (fun t : ℝ => f (x+t • u)) 0| ≤ M) :
    |iteratedDeriv n (fun t : ℝ => f (x+t • h)) 0| ≤ M*s^n := by
  have hu : ‖s⁻¹ • h‖ ≤ 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs)]
    calc
      _ ≤ s⁻¹*s := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hs.le)
      _ = 1 := inv_mul_cancel₀ hs.ne'
  have he : h=s • (s⁻¹ • h) := by rw [smul_smul,mul_inv_cancel₀ hs.ne',one_smul]
  conv_lhs => rw [he,line_derivative_scale,abs_mul,abs_pow,abs_of_pos hs]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hM _ hu) (pow_nonneg hs.le n)

end

section
open Set
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma segment_in_ball {x v : E} {s k t : ℝ} (hs : 0 ≤ s) (hk : 0 ≤ k)
    (hv : ‖v‖ ≤ k) (ht : t ∈ Icc 0 s) : ‖(x+t • v)-x‖ ≤ k*s := by
  rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
  calc
    t*‖v‖ ≤ t*k := mul_le_mul_of_nonneg_left hv ht.1
    _ ≤ s*k := mul_le_mul ht.2 le_rfl hk hs
    _ = k*s := mul_comm _ _

theorem ball_quadratic_remainder (f : E → ℝ) (x v : E) {s k M : ℝ}
    (hs : 0 < s) (hk : 0 < k) (hv : ‖v‖ ≤ k)
    (hf : ∀ y,‖y-x‖ ≤ k*s → ContDiffAt ℝ 3 f y)
    (hM : ∀ y,‖y-x‖ ≤ k*s → ∀ u,‖u‖ ≤ 1 →
      |iteratedDeriv 3 (fun t : ℝ => f (y+t • u)) 0| ≤ M) :
    |f (x+s • v)-(f x+s*(fderiv ℝ f x v)+
      s^2/2*(fderiv ℝ (fderiv ℝ f) x v v))| ≤ (M*k^3)*s^3/6 := by
  apply line_quadratic_remainder hs
  · exact fun t ht => hf _ (segment_in_ball hs.le hk.le hv ht)
  · intro t ht
    exact bounded_directional_derivative 3 f (x+t • v) v hk hv
      (hM _ (segment_in_ball hs.le hk.le hv ⟨ht.1.le,ht.2.le⟩))

end

open scoped BigOperators

lemma quadratic_entrywise_error {N : ℕ} (E : Matrix (Fin N) (Fin N) ℝ) (x : EuclideanSpace ℝ (Fin N))
    {b : ℝ} (hb : 0 ≤ b) (he : ∀ i j,|E i j| ≤ b) :
    |∑ i,∑ j, E i j*x i*x j| ≤ (N:ℝ)*b*‖x‖^2 := by
  have h1 : |∑ i,∑ j, E i j*x i*x j| ≤ ∑ i,∑ j,b * |x i| * |x j| := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j _
    simp only [abs_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (he i j) (abs_nonneg _)) (abs_nonneg _)
  have h2 : (∑ i : Fin N, |x i|)^2 ≤ (N:ℝ)*‖x‖^2 := by
    have h := sq_sum_le_card_mul_sum_sq (s:=Finset.univ) (f:=fun i : Fin N => |x i|)
    simpa only [Finset.card_univ,Fintype.card_fin,sq_abs,EuclideanSpace.real_norm_sq_eq] using h
  apply h1.trans
  have heq : (∑ i,∑ j,b * |x i| * |x j|) = b*(∑ i : Fin N,|x i|)^2 := by
    simp only [pow_two,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  nlinarith [mul_le_mul_of_nonneg_left h2 hb]

lemma mixed_error {fpp fpm fmp fmm f0 gi gj Hi Hj Hij h R e vpp vpm vmp vmm : ℝ}
    (hh : 0 < h)
    (hpp : |fpp-(f0+h*(gi+gj)+h^2/2*(Hi+Hj+2*Hij))| ≤ R)
    (hpm : |fpm-(f0+h*(gi-gj)+h^2/2*(Hi+Hj-2*Hij))| ≤ R)
    (hmp : |fmp-(f0+h*(-gi+gj)+h^2/2*(Hi+Hj-2*Hij))| ≤ R)
    (hmm : |fmm-(f0+h*(-gi-gj)+h^2/2*(Hi+Hj+2*Hij))| ≤ R)
    (vpp' : |vpp-fpp| ≤ e) (vpm' : |vpm-fpm| ≤ e)
    (vmp' : |vmp-fmp| ≤ e) (vmm' : |vmm-fmm| ≤ e) :
    |(vpp-vpm-vmp+vmm)/(4*h^2)-Hij| ≤ (R+e)/h^2 := by
  have hpp' := abs_le.mp hpp
  have hpm' := abs_le.mp hpm
  have hmp' := abs_le.mp hmp
  have hmm' := abs_le.mp hmm
  have vpp'' := abs_le.mp vpp'
  have vpm'' := abs_le.mp vpm'
  have vmp'' := abs_le.mp vmp'
  have vmm'' := abs_le.mp vmm'
  have ha : |vpp-vpm-vmp+vmm-4*h^2*Hij| ≤ 4*(R+e) := by
    rw [abs_le]
    constructor <;> linarith
  have heq : (vpp-vpm-vmp+vmm)/(4*h^2)-Hij =
      (vpp-vpm-vmp+vmm-4*h^2*Hij)/(4*h^2) := by field_simp
  rw [heq,abs_div,abs_of_pos (by positivity : (0:ℝ)<4*h^2)]
  apply (div_le_iff₀ (by positivity : (0:ℝ)<4*h^2)).mpr
  calc
    _ ≤ 4*(R+e) := ha
    _ = (R+e)/h^2*(4*h^2) := by field_simp

end CurrentKS.Difference

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_RationalBasis
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Difference
open Set Matrix
open scoped BigOperators ContDiff

variable {N : ℕ}

lemma pointCast_step (x v : Fin N → ℚ) (h : ℚ) :
    pointCast (x+h • v)=pointCast x+(h:ℝ) • pointCast v := by
  funext i
  simp [pointCast]

lemma pointCast_basis (i : Fin N) : pointCast (rationalBasis i)=realBasis i := by
  funext j
  by_cases he : j=i <;> simp [pointCast,rationalBasis,realBasis,he]

lemma pointCast_add (u v : Fin N → ℚ) : pointCast (u+v)=pointCast u+pointCast v := by
  funext i
  simp [pointCast]

lemma pointCast_neg (u : Fin N → ℚ) : pointCast (-u) = -pointCast u := by
  funext i
  simp [pointCast]

lemma realBasis_bound (i : Fin N) : ‖realBasis i‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro j
  by_cases he : j=i <;> simp [realBasis,he]

lemma stencilHessian_symm (query : (Fin N → ℚ) → ℚ) (x : Fin N → ℚ) (h : ℚ) :
    (stencilHessian query x h).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  dsimp [stencilHessian]
  by_cases hij : i=j
  · subst j; rfl
  · rw [ite_eq_right hij,ite_eq_right (Ne.symm hij)]
    have h1 : rationalBasis j+rationalBasis i=rationalBasis i+rationalBasis j := add_comm _ _
    have h2 : rationalBasis j-rationalBasis i = -rationalBasis i+rationalBasis j := sub_eq_neg_add _ _
    have h3 : -rationalBasis j+rationalBasis i=rationalBasis i-rationalBasis j := (sub_eq_neg_add _ _).symm
    have h4 : -rationalBasis j-rationalBasis i = -rationalBasis i-rationalBasis j := by
      simp only [sub_eq_add_neg,add_comm]
    rw [h1,h2,h3,h4]
    ring

lemma ball_remainder_unit (f : (Fin N → ℝ) → ℝ) (x v : Fin N → ℝ) {h M : ℝ}
    (hh : 0<h) (hv : ‖v‖ ≤ 1)
    (hf : ∀ y,‖y-x‖ ≤ 2*h → ContDiffAt ℝ 3 f y)
    (hM : ∀ y,‖y-x‖ ≤ 2*h → ∀ u,‖u‖ ≤ 1 →
      |iteratedDeriv 3 (fun t : ℝ => f (y+t • u)) 0| ≤ M) :
    |f (x+h • v)-(f x+h*(fderiv ℝ f x v)+
      h^2/2*(fderiv ℝ (fderiv ℝ f) x v v))| ≤ M*h^3/6 := by
  have he := ball_quadratic_remainder f x v hh (by norm_num : (0:ℝ)<1) hv
    (fun y hy => hf y (by linarith)) (fun y hy => hM y (by linarith))
  simpa only [one_pow,mul_one] using he

theorem stencilGradient_error (query : (Fin N → ℚ) → ℚ) (f : (Fin N → ℝ) → ℝ)
    (x : Fin N → ℚ) (h : ℚ) (i : Fin N) {M e : ℝ} (hh : 0<h) (he : 0 ≤ e)
    (hf : ∀ y,‖y-pointCast x‖ ≤ 2*(h:ℝ) → ContDiffAt ℝ 3 f y)
    (hM : ∀ y,‖y-pointCast x‖ ≤ 2*(h:ℝ) → ∀ u,‖u‖ ≤ 1 →
      |iteratedDeriv 3 (fun t : ℝ => f (y+t • u)) 0| ≤ M)
    (hquery : ∀ y,‖pointCast y-pointCast x‖ ≤ 2*(h:ℝ) → |(query y:ℝ)-f (pointCast y)| ≤ e) :
    |(stencilGradient query x h i:ℝ)-fderiv ℝ f (pointCast x) (realBasis i)| ≤
      M*(h:ℝ)^2/6+e/(h:ℝ) := by
  have hhr : (0:ℝ)<h := by exact_mod_cast hh
  have hp := ball_remainder_unit f (pointCast x) (realBasis i) hhr (realBasis_bound i) hf hM
  have hm := ball_remainder_unit f (pointCast x) (-realBasis i) hhr
    (by simpa only [norm_neg] using realBasis_bound i) hf hM
  simp only [map_neg,_root_.neg_apply,neg_neg,smul_neg,mul_neg,← sub_eq_add_neg] at hm
  have hq (v : Fin N → ℚ) (hv : ‖pointCast v‖ ≤ 1) :
      |(stencilValue query x h v:ℝ)-f (pointCast x+(h:ℝ) • pointCast v)| ≤ e := by
    have ht : ‖pointCast (x+h • v)-pointCast x‖ ≤ 2*(h:ℝ) := by
      rw [pointCast_step]
      exact (segment_in_ball hhr.le zero_le_one hv ⟨hhr.le,le_rfl⟩).trans (by linarith)
    simpa only [stencilValue,pointCast_step] using hquery (x+h • v) ht
  have hpq := hq (rationalBasis i) (by simpa only [pointCast_basis] using realBasis_bound i)
  have hmq := hq (-rationalBasis i) (by simpa only [pointCast_neg,pointCast_basis,norm_neg] using realBasis_bound i)
  simp only [pointCast_basis,pointCast_neg,smul_neg,← sub_eq_add_neg] at hpq hmq
  have ht := gradient_error hhr he hp hm hpq hmq
  simpa only [stencilGradient,Rat.cast_div,Rat.cast_sub,Rat.cast_mul,Rat.cast_ofNat] using ht

theorem stencilHessian_diagonal_error (query : (Fin N → ℚ) → ℚ) (f : (Fin N → ℝ) → ℝ)
    (x : Fin N → ℚ) (h : ℚ) (i : Fin N) {M e : ℝ} (hh : 0<h) (he : 0 ≤ e)
    (hf : ∀ y,‖y-pointCast x‖ ≤ 2*(h:ℝ) → ContDiffAt ℝ 3 f y)
    (hM : ∀ y,‖y-pointCast x‖ ≤ 2*(h:ℝ) → ∀ u,‖u‖ ≤ 1 →
      |iteratedDeriv 3 (fun t : ℝ => f (y+t • u)) 0| ≤ M)
    (hquery : ∀ y,‖pointCast y-pointCast x‖ ≤ 2*(h:ℝ) → |(query y:ℝ)-f (pointCast y)| ≤ e) :
    |(stencilHessian query x h i i:ℝ)-fderiv ℝ (fderiv ℝ f) (pointCast x) (realBasis i) (realBasis i)| ≤
      M*(h:ℝ)/3+4*e/(h:ℝ)^2 := by
  have hhr : (0:ℝ)<h := by exact_mod_cast hh
  have hp := ball_remainder_unit f (pointCast x) (realBasis i) hhr (realBasis_bound i) hf hM
  have hm := ball_remainder_unit f (pointCast x) (-realBasis i) hhr
    (by simpa only [norm_neg] using realBasis_bound i) hf hM
  simp only [map_neg,_root_.neg_apply,neg_neg,smul_neg,mul_neg,← sub_eq_add_neg] at hm
  have hq (v : Fin N → ℚ) (hv : ‖pointCast v‖ ≤ 1) :
      |(stencilValue query x h v:ℝ)-f (pointCast x+(h:ℝ) • pointCast v)| ≤ e := by
    have ht : ‖pointCast (x+h • v)-pointCast x‖ ≤ 2*(h:ℝ) := by
      rw [pointCast_step]
      exact (segment_in_ball hhr.le zero_le_one hv ⟨hhr.le,le_rfl⟩).trans (by linarith)
    simpa only [stencilValue,pointCast_step] using hquery (x+h • v) ht
  have hpq := hq (rationalBasis i) (by simpa only [pointCast_basis] using realBasis_bound i)
  have hmq := hq (-rationalBasis i) (by simpa only [pointCast_neg,pointCast_basis,norm_neg] using realBasis_bound i)
  simp only [pointCast_basis,pointCast_neg,smul_neg,← sub_eq_add_neg] at hpq hmq
  have h0 := hquery x (by simp only [sub_self,norm_zero] <;> positivity)
  have ht := diagonal_error hhr he hp hm hpq hmq h0
  simpa only [stencilHessian,ite_true, if_true,Rat.cast_div,Rat.cast_sub,Rat.cast_add,Rat.cast_mul,
    Rat.cast_pow,Rat.cast_ofNat] using ht

lemma pointCast_sub (u v : Fin N → ℚ) : pointCast (u-v)=pointCast u-pointCast v := by
  funext i
  simp [pointCast]

lemma realBasis_pair_bound (i j : Fin N) (si sj : ℝ) (hsi : |si| ≤ 1) (hsj : |sj| ≤ 1) :
    ‖si • realBasis i+sj • realBasis j‖ ≤ 2 := by
  apply (norm_add_le _ _).trans
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs]
  have hi := mul_le_mul hsi (realBasis_bound i) (norm_nonneg _) zero_le_one
  have hj := mul_le_mul hsj (realBasis_bound j) (norm_nonneg _) zero_le_one
  linarith

theorem stencilHessian_mixed_error (query : (Fin N → ℚ) → ℚ) (f : (Fin N → ℝ) → ℝ)
    (x : Fin N → ℚ) (h : ℚ) (i j : Fin N) (hij : i ≠ j) {M e : ℝ} (hh : 0<h)
    (hf : ∀ y,‖y-pointCast x‖ ≤ 2*(h:ℝ) → ContDiffAt ℝ 3 f y)
    (hM : ∀ y,‖y-pointCast x‖ ≤ 2*(h:ℝ) → ∀ u,‖u‖ ≤ 1 →
      |iteratedDeriv 3 (fun t : ℝ => f (y+t • u)) 0| ≤ M)
    (hquery : ∀ y,‖pointCast y-pointCast x‖ ≤ 2*(h:ℝ) → |(query y:ℝ)-f (pointCast y)| ≤ e) :
    |(stencilHessian query x h i j:ℝ)-fderiv ℝ (fderiv ℝ f) (pointCast x) (realBasis i) (realBasis j)| ≤
      (4/3:ℝ)*M*(h:ℝ)+e/(h:ℝ)^2 := by
  have hhr : (0:ℝ)<h := by exact_mod_cast hh
  have ht (v : Fin N → ℝ) (hv : ‖v‖ ≤ 2) :=
    ball_quadratic_remainder f (pointCast x) v hhr (by norm_num : (0:ℝ)<2) hv hf hM
  have hsym := (hf (pointCast x) (by simp only [sub_self,norm_zero] <;> positivity)).isSymmSndFDerivAt
    (by norm_num : minSmoothness ℝ 2 ≤ (3:WithTop ℕ∞))
  have hji := hsym (realBasis j) (realBasis i)
  have hpp := ht (realBasis i+realBasis j) (by
    simpa only [one_smul] using realBasis_pair_bound i j 1 1 (by norm_num) (by norm_num))
  have hpm := ht (realBasis i-realBasis j) (by
    simpa only [one_smul,neg_one_smul,← sub_eq_add_neg] using realBasis_pair_bound i j 1 (-1) (by norm_num) (by norm_num))
  have hmp := ht (-realBasis i+realBasis j) (by
    simpa only [one_smul,neg_one_smul] using realBasis_pair_bound i j (-1) 1 (by norm_num) (by norm_num))
  have hmm := ht (-realBasis i-realBasis j) (by
    simpa only [neg_one_smul,← sub_eq_add_neg] using realBasis_pair_bound i j (-1) (-1) (by norm_num) (by norm_num))
  simp only [map_add,map_sub,map_neg,_root_.add_apply,
    _root_.sub_apply,_root_.neg_apply,hji] at hpp hpm hmp hmm
  have hlin : ∀ a b c : ℝ, a+b+(b+c)=a+c+2*b := by intros; ring
  have hlin2 : ∀ a b c : ℝ, a-b-(b-c)=a+c-2*b := by intros; ring
  have hlin3 : ∀ a b c : ℝ, -(-a+b)+(-b+c)=a+c-2*b := by intros; ring
  have hlin4 : ∀ a b c : ℝ, -(-a-b)-(-b-c)=a+c+2*b := by intros; ring
  rw [hlin] at hpp
  rw [hlin2] at hpm
  rw [hlin3] at hmp
  rw [hlin4] at hmm
  have hq (v : Fin N → ℚ) (hv : ‖pointCast v‖ ≤ 2) :
      |(stencilValue query x h v:ℝ)-f (pointCast x+(h:ℝ) • pointCast v)| ≤ e := by
    have hb : ‖pointCast (x+h • v)-pointCast x‖ ≤ 2*(h:ℝ) := by
      rw [pointCast_step]
      exact segment_in_ball hhr.le (by norm_num) hv ⟨hhr.le,le_rfl⟩
    simpa only [stencilValue,pointCast_step] using hquery (x+h • v) hb
  have hqpp := hq (rationalBasis i+rationalBasis j) (by
    rw [pointCast_add,pointCast_basis,pointCast_basis]
    simpa only [one_smul] using realBasis_pair_bound i j 1 1 (by norm_num) (by norm_num))
  have hqpm := hq (rationalBasis i-rationalBasis j) (by
    rw [pointCast_sub,pointCast_basis,pointCast_basis]
    simpa only [one_smul,neg_one_smul,← sub_eq_add_neg] using realBasis_pair_bound i j 1 (-1) (by norm_num) (by norm_num))
  have hqmp := hq (-rationalBasis i+rationalBasis j) (by
    rw [pointCast_add,pointCast_neg,pointCast_basis,pointCast_basis]
    simpa only [one_smul,neg_one_smul] using realBasis_pair_bound i j (-1) 1 (by norm_num) (by norm_num))
  have hqmm := hq (-rationalBasis i-rationalBasis j) (by
    rw [pointCast_sub,pointCast_neg,pointCast_basis,pointCast_basis]
    simpa only [neg_one_smul,← sub_eq_add_neg] using realBasis_pair_bound i j (-1) (-1) (by norm_num) (by norm_num))
  simp only [pointCast_add,pointCast_sub,pointCast_neg,pointCast_basis] at hqpp hqpm hqmp hqmm
  have hm := mixed_error hhr hpp hpm hmp hmm hqpp hqpm hqmp hqmm
  have heq : ((M*(2:ℝ)^3)*(h:ℝ)^3/6+e)/(h:ℝ)^2 = (4/3:ℝ)*M*(h:ℝ)+e/(h:ℝ)^2 := by
    field_simp
    ring
  rw [heq] at hm
  simpa only [stencilHessian,ite_eq_right hij,Rat.cast_div,Rat.cast_sub,Rat.cast_add,Rat.cast_mul,
    Rat.cast_pow,Rat.cast_ofNat] using hm

end CurrentKS.Difference

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_StencilScalarBounds
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Difference
open Matrix
open scoped BigOperators ContDiff

variable {N : ℕ}

lemma stencil_scalar_bounds {a M n h : ℝ} (ha : 0 < a) (hM : 1 ≤ M)
    (hn : 1 ≤ n) (hh : 0 < h) (hh1 : h ≤ 1) (hhsmall : h ≤ a/(64*M*n)) :
    M*h^2/6+(a*h^2/(128*n))/h ≤ a/8 ∧
    M*h/3+4*(a*h^2/(128*n))/h^2 ≤ 7*a/(192*n) ∧
    (4/3:ℝ)*M*h+(a*h^2/(128*n))/h^2 ≤ 7*a/(192*n) := by
  have hn0 : 0 < n := by linarith
  have hMp : 0 < M := by linarith
  have hs : M*h ≤ a/(64*n) := by
    apply (le_div_iff₀ (by positivity : (0:ℝ)<64*n)).mpr
    have ht := (le_div_iff₀ (by positivity : (0:ℝ)<64*M*n)).mp hhsmall
    nlinarith
  have he1 : (a*h^2/(128*n))/h = a*h/(128*n) := by field_simp
  have he2 : (a*h^2/(128*n))/h^2 = a/(128*n) := by field_simp
  have he3 : 4*(a*h^2/(128*n))/h^2 = a/(32*n) := by field_simp <;> ring
  rw [he1,he2,he3]
  have hs0 : M*h ≤ a/64 := hs.trans (by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<64*n)).mpr
    nlinarith)
  have hs2 : M*h^2 ≤ a/64 := by
    have h0 : 0 ≤ M*h := by positivity
    have ht := mul_le_mul_of_nonneg_left hh1 h0
    nlinarith
  have he : a*h/(128*n) ≤ a/128 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<128*n)).mpr
    nlinarith
  refine ⟨by linarith,?_,?_⟩
  · have he : a/(64*n)/3+a/(32*n)=7*a/(192*n) := by field_simp <;> ring
    calc
      _ ≤ a/(64*n)/3+a/(32*n) := by linarith
      _ = _ := he
  · have he : (4/3:ℝ)*(a/(64*n))+a/(128*n)=11*a/(384*n) := by field_simp <;> ring
    calc
      _ ≤ (4/3:ℝ)*(a/(64*n))+a/(128*n) := by linarith
      _ = 11*a/(384*n) := he
      _ ≤ 7*a/(192*n) := by
        have : 7*a/(192*n)-11*a/(384*n)=a/(128*n) := by field_simp <;> ring
        have hp : 0 ≤ a/(128*n) := by positivity
        linarith

theorem computed_stencil_accuracy [NeZero N]
    (query : (Fin N → ℚ) → ℚ) (f : (Fin N → ℝ) → ℝ) (x : Fin N → ℚ)
    {h : ℚ} {a M : ℝ} (ha : 0 < a) (hM1 : 1 ≤ M) (hh : 0<h)
    (hh1 : (h:ℝ) ≤ 1) (hhsmall : (h:ℝ) ≤ a/(64*M*N))
    (hf : ∀ y,‖y-pointCast x‖ ≤ 2*(h:ℝ) → ContDiffAt ℝ 3 f y)
    (hM : ∀ y,‖y-pointCast x‖ ≤ 2*(h:ℝ) → ∀ u,‖u‖ ≤ 1 →
      |iteratedDeriv 3 (fun t : ℝ => f (y+t • u)) 0| ≤ M)
    (hquery : ∀ y,‖pointCast y-pointCast x‖ ≤ 2*(h:ℝ) →
      |(query y:ℝ)-f (pointCast y)| ≤ a*(h:ℝ)^2/(128*N)) :
    (∀ i,|(stencilGradient query x h i:ℝ)-fderiv ℝ f (pointCast x) (realBasis i)| ≤ a/8) ∧
    (∀ i j,|(stencilHessian query x h i j:ℝ)-
      fderiv ℝ (fderiv ℝ f) (pointCast x) (realBasis i) (realBasis j)| ≤ 7*a/(192*N)) := by
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  have he : 0 ≤ a*(h:ℝ)^2/(128*N) := by positivity
  have hs := stencil_scalar_bounds ha hM1 hNr (by exact_mod_cast hh) hh1 hhsmall
  constructor
  · intro i
    exact (stencilGradient_error query f x h i hh he hf hM hquery).trans hs.1
  · intro i j
    by_cases hij : i=j
    · subst j
      exact (stencilHessian_diagonal_error query f x h i hh he hf hM hquery).trans hs.2.1
    · exact (stencilHessian_mixed_error query f x h i j hij hh hf hM hquery).trans hs.2.2

lemma linear_basis_expansion (L : (Fin N → ℝ) →L[ℝ] ℝ) (u : Fin N → ℝ) :
    L u = ∑ i,L (realBasis i)*u i := by
  have hu : u=∑ i,u i • realBasis i := by
    ext j
    simp [realBasis,Pi.single_apply]
  conv_lhs => rw [hu]
  simp only [map_sum,map_smul,smul_eq_mul,mul_comm]

lemma bilinear_basis_expansion (B : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℝ)
    (u : Fin N → ℝ) : B u u=∑ i,∑ j,B (realBasis i) (realBasis j)*u i*u j := by
  rw [linear_basis_expansion (B u) u]
  have hb j : B u (realBasis j)=∑ i,B (realBasis i) (realBasis j)*u i := by
    exact linear_basis_expansion ((ContinuousLinearMap.apply ℝ ℝ (realBasis j)).comp B) u
  simp_rw [hb,Finset.sum_mul]
  exact Finset.sum_comm

theorem stencil_quadratic_accuracy (H : Matrix (Fin N) (Fin N) ℚ)
    (B : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℝ) {a : ℝ} (ha : 0 ≤ a)
    (herr : ∀ i j,|(H i j:ℝ)-B (realBasis i) (realBasis j)| ≤ 7*a/(192*N))
    (u : EuclideanSpace ℝ (Fin N)) :
    |u ⬝ᵥ ((H.map fun t : ℚ => (t:ℝ))*ᵥ u)-B u u| ≤ a/16*‖u‖^2 := by
  have hn : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hb : 0 ≤ 7*a/(192*N) := by positivity
  have he := quadratic_entrywise_error
    (fun i j => (H i j:ℝ)-B (realBasis i) (realBasis j)) u hb herr
  have heq : u ⬝ᵥ ((H.map fun t : ℚ => (t:ℝ))*ᵥ u)-B u u=
      ∑ i,∑ j,((H i j:ℝ)-B (realBasis i) (realBasis j))*u i*u j := by
    rw [bilinear_basis_expansion]
    simp only [dotProduct,mulVec,Matrix.map_apply,Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  apply he.trans
  by_cases hN : N=0
  · simp only [hN,Nat.cast_zero,mul_zero,div_zero,zero_mul]
    positivity
  · have hNr : (N:ℝ) ≠ 0 := by exact_mod_cast hN
    have hc : (N:ℝ)*(7*a/(192*N))=7*a/192 := by field_simp
    rw [hc]
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)

end CurrentKS.Difference

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_EuclideanForget
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Difference
open scoped ContDiff

theorem symmetric_bilinear_norm_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hsymm : ∀ u v,B u v=B v u) (hquad : ∀ u,|B u u| ≤ M*‖u‖^2) : ‖B‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hM
  intro u hu
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hM
  intro v hv
  have hp := hquad (u+v)
  have hm := hquad (u-v)
  have hid : B (u+v) (u+v)-B (u-v) (u-v)=4*B u v := by
    simp only [map_add,map_sub,_root_.add_apply,_root_.sub_apply,hsymm v u]
    ring
  have hineq := (abs_sub (B (u+v) (u+v)) (B (u-v) (u-v))).trans (add_le_add hp hm)
  rw [hid,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<4)] at hineq
  have hpara := parallelogram_law_with_norm ℝ u v
  rw [hu,hv] at hpara
  rw [Real.norm_eq_abs]
  nlinarith

variable {N : ℕ}

lemma euclideanForget_bound (u : EuclideanSpace ℝ (Fin N)) : ‖euclideanForget u‖ ≤ ‖u‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  exact PiLp.norm_apply_le u i

theorem actual_hessian_norm (f : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hf : ContDiffAt ℝ 2 f x)
    (hder : ∀ u,‖u‖ ≤ 1 → |iteratedDeriv 2 (fun t : ℝ => f (x+t • u)) 0| ≤ M) :
    ‖euclideanBilinear (fderiv ℝ (fderiv ℝ f) x)‖ ≤ M := by
  apply symmetric_bilinear_norm_le _ hM
  · intro u v
    exact hf.isSymmSndFDerivAt (by norm_num) u v
  · intro u
    by_cases hu : u=0
    · subst u
      simp only [map_zero,abs_zero,norm_zero,zero_pow (by decide : 2≠0),mul_zero,le_refl]
    · have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
      have hh := bounded_directional_derivative 2 f x (euclideanForget u) hn (euclideanForget_bound u) hder
      have hfx : ContDiffAt ℝ 2 f (x+(0:ℝ) • euclideanForget u) := by simpa using hf
      have hid := second_deriv_line (x:=x) (h:=euclideanForget u) (t:=0) hfx
      rw [iteratedDeriv_succ,iteratedDeriv_one] at hh
      rw [hid,zero_smul,add_zero] at hh
      exact hh

open CurrentKS.RationalRoot Matrix Set

lemma gradient_mem_candidates [NeZero N] (query : (Fin N → ℚ) → ℚ) (x : Fin N → ℚ)
    (h a M s ρ : ℚ) :
    x+s • rationalGradientDirection (stencilGradient query x h) ∈ interiorCandidates query x h a M s ρ := by
  exact List.mem_cons_self

lemma curvature_mem_candidates [NeZero N] (query : (Fin N → ℚ) → ℚ) (x q : Fin N → ℚ)
    (h a M s ρ : ℚ) (hq : computedCurvature (stencilHessian query x h) a M s ρ=some q) :
    x+q ∈ interiorCandidates query x h a M s ρ ∧ x-q ∈ interiorCandidates query x h a M s ρ := by
  simp [interiorCandidates,hq]

lemma pointCast_gradient [NeZero N] (x g : Fin N → ℚ) (s : ℚ) :
    pointCast (x+s • rationalGradientDirection g)=pointCast x+(s:ℝ) • gradientDirection g := by
  rw [pointCast_step]
  have hh : pointCast (rationalGradientDirection g)=gradientDirection g := rationalGradientDirection_cast g
  rw [hh]

theorem interiorCandidates_progress [NeZero N]
    (query : (Fin N → ℚ) → ℚ) (f : (Fin N → ℝ) → ℝ) (x : Fin N → ℚ)
    (h a M s ρ : ℚ) (ha : 0 < a) (ha1 : a ≤ 1) (hM1 : 1 ≤ M)
    (hs : 0 < s) (hs1 : s ≤ 1/4) (hstep : M*s ≤ a/4) (hh : 0 < h) (hh1 : h ≤ 1)
    (hhsmall : h ≤ a/(64*M*N)) (hρ : 0 < ρ)
    (hmesh : (N:ℚ)*ρ/2 ≤ s*(a/(1024*M))/8)
    (hf : ∀ y,‖y-pointCast x‖ ≤ (s:ℝ)+2*(h:ℝ) → ContDiffAt ℝ 3 f y)
    (hders : ∀ y,‖y-pointCast x‖ ≤ (s:ℝ)+2*(h:ℝ) → ∀ u,‖u‖ ≤ 1 →
      |iteratedDeriv 2 (fun t : ℝ => f (y+t • u)) 0| ≤ (M:ℝ) ∧
      |iteratedDeriv 3 (fun t : ℝ => f (y+t • u)) 0| ≤ (M:ℝ))
    (hquery : ∀ y,‖pointCast y-pointCast x‖ ≤ 2*(h:ℝ) →
      |(query y:ℝ)-f (pointCast y)| ≤ (a:ℝ)*(h:ℝ)^2/(128*N))
    (hprogress : (∃ i,(a:ℝ) ≤ |fderiv ℝ f (pointCast x) (realBasis i)|) ∨
      ¬ ∀ u,0 ≤ realQuadratic (stencilHessian query x h) u+7*(a:ℝ)*‖u‖^2) :
    ∃ y∈interiorCandidates query x h a M s ρ,
      f (pointCast y) ≤ f (pointCast x)-2*(a:ℝ)*(s:ℝ)^2 := by
  have har : (0:ℝ) < a := by exact_mod_cast ha
  have hsr : (0:ℝ) < s := by exact_mod_cast hs
  have hhr : (0:ℝ) < h := by exact_mod_cast hh
  have hMr : (0:ℝ) ≤ M := by exact_mod_cast (le_trans (by norm_num : (0:ℚ) ≤ 1) hM1)
  have hacc := computed_stencil_accuracy query f x har (by exact_mod_cast hM1)
    hh (by exact_mod_cast hh1) (by exact_mod_cast hhsmall)
    (fun y hy => hf y (by linarith))
    (fun y hy u hu => (hders y (by linarith) u hu).2) hquery
  have hcenter : ‖pointCast x-pointCast x‖ ≤ (s:ℝ)+2*(h:ℝ) := by
    simp only [sub_self,norm_zero] <;> positivity
  rcases hprogress with hlarge|hnegative
  · let g := stencilGradient query x h
    have hs1r : (s:ℝ) ≤ (1:ℝ)/4 := by
      have ht : (s:ℝ) ≤ ((1/4:ℚ):ℝ) := Rat.cast_le.mpr hs1
      simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using ht
    have he := gradient_candidate_decrease f (pointCast x) g (M:=(M:ℝ)) har hsr
      hs1r (by exact_mod_cast hstep) hacc.1 hlarge
      (fun t ht => (hf _ (by
        have hb := segment_in_ball (x:=pointCast x) hsr.le zero_le_one (gradientDirection_bound g) ht
        linarith)).of_le (by norm_num))
      (fun t ht => (hders _ (by
        have hb := segment_in_ball (x:=pointCast x) hsr.le zero_le_one (gradientDirection_bound g) ⟨ht.1.le,ht.2.le⟩
        linarith) _ (gradientDirection_bound g)).1)
    refine ⟨x+s • rationalGradientDirection g,gradient_mem_candidates query x h a M s ρ,?_⟩
    rw [pointCast_gradient]
    nlinarith [sq_nonneg (s:ℝ)]
  · let H := stencilHessian query x h
    let B := euclideanBilinear (fderiv ℝ (fderiv ℝ f) (pointCast x))
    have hBn : ‖B‖ ≤ (M:ℝ) := actual_hessian_norm f _ hMr
      ((hf _ hcenter).of_le (by norm_num)) (fun u hu => (hders _ hcenter u hu).1)
    have hBe : ∀ u,|realQuadratic H u-B u u| ≤ (a:ℝ)/16*‖u‖^2 := by
      intro u
      exact stencil_quadratic_accuracy H _ har.le hacc.2 u
    have hc := computedCurvature_spec H (stencilHessian_symm query x h) B a M s ρ
      ha ha1 hM1 hs.le hρ hmesh hBn hBe
    cases he : computedCurvature H a M s ρ with
    | none =>
      simp only [he] at hc
      exact False.elim (hnegative hc)
    | some q =>
      simp only [he] at hc
      have hqnorm : ‖pointCast q‖ ≤ (s:ℝ) :=
        (euclideanForget_bound (realVector q)).trans hc.1
      have hqnorm' : ∀ v∈({pointCast q,-pointCast q}:Set (Fin N → ℝ)),‖v‖ ≤ (s:ℝ) := by
        intro v hv
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hv
        rcases hv with rfl|rfl
        · exact hqnorm
        · simpa only [norm_neg] using hqnorm
      have hseg (v : Fin N → ℝ) (hv : v∈({pointCast q,-pointCast q}:Set (Fin N → ℝ)))
          (t : ℝ) (ht : t∈Icc 0 1) : ‖pointCast x+t • v-pointCast x‖ ≤ (s:ℝ)+2*(h:ℝ) := by
        have hb := segment_in_ball (by norm_num : (0:ℝ) ≤ 1) hsr.le (hqnorm' v hv) ht (x:=pointCast x)
        linarith
      have hdec := opposite_candidates_decrease f (pointCast x) (pointCast q) har hsr
        (by exact_mod_cast hstep) hc.2
        (fun v hv t ht => hf _ (hseg v hv t ht))
        (fun v hv t ht => bounded_directional_derivative 3 f _ v hsr (hqnorm' v hv)
          (fun u hu => (hders _ (hseg v hv t ⟨ht.1.le,ht.2.le⟩) u hu).2))
      have hm := curvature_mem_candidates query x q h a M s ρ he
      rcases hdec with hd|hd
      · exact ⟨x+q,hm.1,by simpa only [pointCast_add] using hd⟩
      · exact ⟨x-q,hm.2,by simpa only [pointCast_sub] using hd⟩

end CurrentKS.Difference

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_EndpointCandidates
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State.LightPoint
noncomputable section
open CurrentKS.Difference CurrentKS.RationalRoot
open scoped ContDiff

variable {d N : ℕ} (p : LightPoint d N)

theorem computed_candidates_progress_oai [NeZero d] [NeZero N]
    (query : (Fin N → ℚ) → ℚ) (x : Fin N → ℚ) (hpx : p.x=pointCast x)
    (lam : ℝ) (h a M s ρ : ℚ) (ha : 0<a) (ha1 : a≤1) (hM1 : 1≤M)
    (hrel : lam=512*(a:ℝ)*p.C1^2)
    (hs : 0 < s) (hs1 : s≤1/4) (hstep : M*s≤a/4) (hh : 0<h) (hh1 : h≤1)
    (hhsmall : h≤a/(64*M*N)) (hρ : 0<ρ) (hmesh : (N:ℚ)*ρ/2 ≤ s *(a/(1024*M))/8)
    (hreg : ∀ y,‖y-pointCast x‖≤(s:ℝ)+2*(h:ℝ) → ContDiffAt ℝ 3 (p.Psi lam) y)
    (hders : ∀ y,‖y-pointCast x‖≤(s:ℝ)+2*(h:ℝ) → ∀ u,‖u‖≤1 →
      |iteratedDeriv 2 (fun t : ℝ => p.Psi lam (y+t • u)) 0|≤(M:ℝ) ∧
      |iteratedDeriv 3 (fun t : ℝ => p.Psi lam (y+t • u)) 0|≤(M:ℝ))
    (hquery : ∀ y,‖pointCast y-pointCast x‖≤2*(h:ℝ) →
      |(query y:ℝ)-p.Psi lam (pointCast y)|≤(a:ℝ)*(h:ℝ)^2/(128*N)) :
    ∃ y∈interiorCandidates query x h a M s ρ,
      p.Psi lam (pointCast y)≤p.Psi lam p.x-2*(a:ℝ)*(s:ℝ)^2 := by
  have har : (0:ℝ)<a := by exact_mod_cast ha
  have hsr : (0:ℝ) < s := by exact_mod_cast hs
  have hacc := computed_stencil_accuracy query (p.Psi lam) x har (by exact_mod_cast hM1)
    hh (by exact_mod_cast hh1) (by exact_mod_cast hhsmall)
    (fun y hy => hreg y (by linarith))
    (fun y hy u hu => (hders y (by linarith) u hu).2) hquery
  have hp : (∃ i,(a:ℝ)≤|fderiv ℝ (p.Psi lam) (pointCast x) (realBasis i)|) ∨
      ¬∀ u,0 ≤ realQuadratic (stencilHessian query x h) u+7*(a:ℝ)*‖u‖^2 := by
    by_cases hg : ∃ i,(a:ℝ)≤|fderiv ℝ (p.Psi lam) (pointCast x) (realBasis i)|
    · exact Or.inl hg
    right
    have hgrad : ∀ i,|fderiv ℝ (p.Psi lam) p.x (Pi.single i (1:ℝ))|≤(a:ℝ) := by
      intro i
      rw [hpx]
      exact le_of_lt (lt_of_not_ge fun h => hg ⟨i,h⟩)
    let test : Coordinates N → ℝ := fun u =>
      realQuadratic (stencilHessian query x h) (WithLp.toLp 2 u)
    have herr : ∀ u,|test u-fderiv ℝ (fderiv ℝ (p.Psi lam)) p.x u u|≤
        (a:ℝ)/16*(∑ i,u i^2) := by
      intro u
      have he := stencil_quadratic_accuracy (stencilHessian query x h)
        (fderiv ℝ (fderiv ℝ (p.Psi lam)) (pointCast x)) har.le hacc.2 (WithLp.toLp 2 u)
      simpa only [test,hpx,realQuadratic,EuclideanSpace.real_norm_sq_eq,WithLp.ofLp_toLp] using he
    have hnot := p.shifted_hessian_not_psd har hrel test hgrad herr
    intro hpsd
    apply hnot
    intro u
    have hh := hpsd (WithLp.toLp 2 u)
    simpa only [test,EuclideanSpace.real_norm_sq_eq,WithLp.ofLp_toLp] using hh
  have ht := interiorCandidates_progress query (p.Psi lam) x h a M s ρ ha ha1 hM1 hs hs1
    hstep hh hh1 hhsmall hρ hmesh hreg hders hquery hp
  simpa only [hpx] using ht

end
end CurrentKS.State.LightPoint

end OAI
end

theorem solution : type_of% @OAI.CurrentKS.State.LightPoint.computed_candidates_progress_oai := @OAI.CurrentKS.State.LightPoint.computed_candidates_progress_oai
