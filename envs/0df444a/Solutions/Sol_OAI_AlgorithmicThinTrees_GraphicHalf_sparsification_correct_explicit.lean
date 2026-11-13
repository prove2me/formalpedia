-- Prove2me | solution 1 for OAI.AlgorithmicThinTrees.GraphicHalf.sparsification_correct_explicit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:08:48.370309+00:00
-- url     : https://prove2.me/submissions/c33cbca4-925d-40a2-95ba-86c3a009d70b

import Mathlib
import Definitions.Def_AlgorithmicThinTrees
import Definitions.Def_OAIQ241TT009
import Theorems.Thm_OAI_AlgorithmicThinTrees_GraphicHalf_half_bounds
import Theorems.Thm_OAI_AlgorithmicThinTrees_MetricTests_RationalStep_shortcut_correct_explicit


set_option autoImplicit false

namespace Q339.Numeric
open OAI OAI.StrongThinTree.ShortcutNumeric OAI.StrongThinTree.MultiGraph.Hierarchy

lemma le_of_log_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : Real.log a ≤ Real.log b) : a ≤ b :=
  (Real.log_le_log_iff ha hb).1 h

/-- `log a ≤ m log 2` from `a ≤ 2^m`. -/
lemma log_le_two_pow {a : ℝ} (ha : 0 < a) (m : ℕ) (h : a ≤ (2:ℝ) ^ m) :
    Real.log a ≤ (m:ℝ) * Real.log 2 := by
  have := Real.log_le_log ha h
  rwa [Real.log_pow] at this

/-! ### Basic facts for `x ≥ 2^2000`. Throughout, `c = log 2` and `ℓ = log x`. -/

/-! ### The seven fields. -/

theorem numeric_explicit (r : ℕ) (hr : 2 ^ 2048 ≤ r) :
    OAI.AlgorithmicThinTrees.GraphicHalf.Numeric r := by
  have hc1 := Real.log_two_gt_d9
  have hc2 := Real.log_two_lt_d9
  have hrR : (2:ℝ) ^ 2048 ≤ (r:ℝ) := by exact_mod_cast hr
  have hr0 : 0 < (r:ℝ) := lt_of_lt_of_le (by positivity) hrR
  have hℓ : 2048 * Real.log 2 ≤ Real.log r := by
    have := Real.log_le_log (by positivity) hrR
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hu0 : 0 < (r:ℝ) ^ (-1/16:ℝ) := Real.rpow_pos_of_pos hr0 _
  have hul : Real.log ((r:ℝ) ^ (-1/16:ℝ)) = (-1/16) * Real.log r := Real.log_rpow hr0 _
  have hr32 : (32:ℝ) ≤ r := le_trans
    (le_trans (by norm_num) (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by norm_num : 5 ≤ 2048))) hrR
  have h4 : 4 ≤ r := by exact_mod_cast (by linarith only [hr32] : (4:ℝ) ≤ r)
  clear hr hrR
  refine ⟨h4, ?_, ?_, ?_⟩
  · unfold OAI.StrongThinTree.errorU
    apply le_of_log_le hu0 (by norm_num)
    rw [hul, one_div, Real.log_inv, show (128:ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
    push_cast; linarith
  · unfold OAI.StrongThinTree.errorU
    apply le_of_log_le (by positivity) hu0
    rw [hul, Real.log_div (by norm_num) hr0.ne', show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; linarith
  · unfold OAI.AlgorithmicThinTrees.GraphicHalf.halfError
      OAI.AlgorithmicThinTrees.GraphicHalf.varianceBound OAI.StrongThinTree.errorU
    have hv0 : 0 < (r:ℝ) ^ (-1/4:ℝ) := Real.rpow_pos_of_pos hr0 _
    apply le_of_log_le (by positivity) hu0
    have h20 := log_le_two_pow (a := 20) (by norm_num) 5 (by norm_num)
    have h10 := log_le_two_pow (a := 10) (by norm_num) 4 (by norm_num)
    push_cast at h20 h10
    rw [hul, Real.log_mul (by norm_num) (by positivity), Real.log_sqrt (by positivity),
      ← mul_assoc, Real.log_mul (by norm_num) hv0.ne', Real.log_rpow hr0]
    norm_num
    linarith

end Q339.Numeric

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_BitSupport
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.RationalBits

lemma Parts.mono {b c:ℕ} {q:ℚ} (hq:Parts b q) (hbc:b ≤ c) : Parts c q :=
  ⟨hq.1.trans (Nat.pow_le_pow_right (by decide) hbc),
    hq.2.trans (Nat.pow_le_pow_right (by decide) hbc)⟩
lemma Parts.mul {b c:ℕ} {q r:ℚ} (hq:Parts b q) (hr:Parts c r) : Parts (b+c) (q*r) :=
  KS.W30.mul_parts_le_two_pow q r b c hq.1 hq.2 hr.1 hr.2
lemma Parts.add {b c:ℕ} {q r:ℚ} (hq:Parts b q) (hr:Parts c r) : Parts (b+c+1) (q+r) := by
  have h := KS.W30.add_parts_le_two_pow q r b c hq.1 hq.2 hr.1 hr.2
  exact ⟨h.1,h.2.trans (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))⟩
lemma Parts.inv {b:ℕ} {q:ℚ} (hq:Parts b q) : Parts b q⁻¹ :=
  KS.W30.inv_parts_le_two_pow q b hq.1 hq.2
lemma Parts.neg {b:ℕ} {q:ℚ} (hq:Parts b q) : Parts b (-q) := by
  simpa only [Parts,Rat.neg_num,Int.natAbs_neg,Rat.neg_den] using hq

end CurrentKS.RationalBits

namespace CurrentKS.RationalBits
open scoped BigOperators

lemma parts_one : Parts 0 (1:ℚ) := by norm_num [Parts]

end CurrentKS.RationalBits

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
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_StoredBits
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.RationalBits
open CurrentKS.RationalGridSize

lemma Parts.natCast {b n : ℕ} (hn : n ≤ 2^b) : Parts b (n:ℚ) := by
  constructor
  · simpa only [Rat.num_natCast,Int.natAbs_natCast] using hn
  · simpa only [Rat.den_natCast] using Nat.one_le_two_pow

lemma natCast_parts (n : ℕ) : Parts n.size (n:ℚ) := Parts.natCast (Nat.lt_size_self n).le

end CurrentKS.RationalBits

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

lemma cutIndicator_binary (S : Finset (Fin n)) (v : Fin n) :
    cutIndicator S v=0 ∨ cutIndicator S v=1 := by
  by_cases hv : v ∈ S <;> simp [cutIndicator,hv]

end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Matrix
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι

section
open Matrix
namespace StrongThinTree
section Resistance
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma rankOne_quadratic (b x : ι → ℝ) :
    x ⬝ᵥ (vecMulVec b b *ᵥ x) = (b ⬝ᵥ x) ^ 2 := by
  rw [vecMulVec_mulVec]
  simp [dotProduct, Finset.mul_sum, pow_two, mul_comm, mul_left_comm]

lemma posDef_solve {X : Matrix ι ι ℝ} (hX : X.PosDef) (b : ι → ℝ) :
    X *ᵥ (X⁻¹ *ᵥ b) = b := by
  rw [mulVec_mulVec, mul_nonsing_inv X ((isUnit_iff_isUnit_det X).mp hX.isUnit),
    one_mulVec]

theorem resistance_order {X : Matrix ι ι ℝ} (hX : X.PosDef)
    (b : ι → ℝ) {t : ℝ} (ht : 0 < t) :
    b ⬝ᵥ (X⁻¹ *ᵥ b) ≤ t ↔ (t • X - vecMulVec b b).PosSemidef := by
  let y := X⁻¹ *ᵥ b
  have hsolve : X *ᵥ y = b := posDef_solve hX b
  have hq (x : ι → ℝ) : 0 ≤ x ⬝ᵥ (X *ᵥ x) := by
    simpa only [star_trivial] using hX.posSemidef.dotProduct_mulVec_nonneg x
  have hr : 0 ≤ b ⬝ᵥ y := by
    simpa only [hsolve, dotProduct_comm] using hq y
  constructor
  · intro h
    have hb : (vecMulVec b b).IsHermitian := by
      simpa only [star_trivial] using (posSemidef_vecMulVec_self_star b).isHermitian
    refine PosSemidef.of_dotProduct_mulVec_nonneg
      ((hX.isHermitian.smul (isSelfAdjoint_iff.mpr (star_trivial t))).sub hb) ?_
    intro x
    have hcs := quadratic_cauchy_schwarz hX.posSemidef x y
    rw [hsolve] at hcs
    have hm : (x ⬝ᵥ (X *ᵥ x)) * (b ⬝ᵥ y) ≤ (x ⬝ᵥ (X *ᵥ x)) * t :=
      mul_le_mul_of_nonneg_left h (hq x)
    rw [dotProduct_comm y b, dotProduct_comm x b] at hcs
    simp only [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul,
      smul_eq_mul, rankOne_quadratic]
    nlinarith
  · intro h
    have htest := h.dotProduct_mulVec_nonneg y
    simp only [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul,
      smul_eq_mul, rankOne_quadratic, hsolve, dotProduct_comm y b] at htest
    change b ⬝ᵥ y ≤ t
    nlinarith

end Resistance
end StrongThinTree

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_GraphMatrix
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.Partitions.mem_crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV

section

noncomputable section
open Matrix Finset
open scoped MatrixOrder
namespace StrongThinTree
variable {V : Type uV} [Fintype V] [DecidableEq V]
omit [DecidableEq V] in
lemma qform_sub (X Y : Matrix V V ℝ) (v : V → ℝ) : qform (X-Y) v=qform X v-qform Y v := by
  simp [qform,sub_mulVec,dotProduct_sub]
omit [DecidableEq V] in
lemma qform_smul (a : ℝ) (X : Matrix V V ℝ) (v : V → ℝ) : qform (a • X) v=a*qform X v := by
  simp [qform,smul_mulVec,dotProduct_smul]
omit [DecidableEq V] in
lemma qform_mono {X Y : Matrix V V ℝ} (h : X ≤ Y) (v : V → ℝ) : qform X v ≤ qform Y v := by
  have hh := qform_nonneg (Matrix.le_iff.mp h) v
  rw [qform_sub] at hh
  linarith

namespace MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)
lemma laplacian_qform (F : Finset (Fin m)) (v : Fin n → ℝ) :
    qform (G.laplacian F) v=∑e ∈ F, (v (G.left e)-v (G.right e))^2 := by
  simp only [laplacian,qform,sum_mulVec,dotProduct_sum,rankOne_quadratic]
  apply sum_congr rfl
  intro e _
  rw [dotProduct_comm]
  congr 1
  exact G.eval_incidence v e
lemma laplacian_cut (F : Finset (Fin m)) (S : Finset (Fin n)) :
    qform (G.laplacian F) (cutIndicator S)=(G.cut F S).card := by
  rw [G.laplacian_qform]
  simp only [cut,card_eq_sum_ones,Nat.cast_sum,sum_filter]
  apply sum_congr rfl
  intro e _
  by_cases hl : G.left e ∈ S <;> by_cases hr : G.right e ∈ S <;> simp [cutIndicator,hl,hr]

end MultiGraph
end StrongThinTree

end
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_BasePacking
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Hermitian.instFiniteDimensionalRealSubtypeMatMemSubmoduleH
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.Partitions.mem_crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uI uV uI2

section

noncomputable section
open Finset Submodule
namespace StrongThinTree.Packing

variable {E : Type uE} {I : Type uI} {V : Type uV} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
  [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

omit [Fintype E] [DecidableEq E] [FiniteDimensional ℝ V] in
lemma span_mono (v : E → V) {s t : Finset E} (h : s ⊆ t) : span v s ≤ span v t :=
  Submodule.span_mono (Set.image_mono h)

omit [Fintype E] [FiniteDimensional ℝ V] in
lemma span_insert (v : E → V) (s : Finset E) (e : E) :
    span v (insert e s) = Submodule.span ℝ (insert (v e) (v '' (s : Set E))) := by
  simp only [span, coe_insert, Set.image_insert_eq]

omit [Fintype E] [DecidableEq E] [FiniteDimensional ℝ V] in
lemma indep_rank (v : E → V) {s : Finset E} (hs : LinearIndepOn ℝ v s) :
    Module.finrank ℝ (span v s) = s.card := by
  have heq : Set.range (fun e : (s : Set E) => v e) = v '' (s : Set E) := by
    ext x; simp
  have h := finrank_span_eq_card hs.linearIndependent
  change Module.finrank ℝ (Submodule.span ℝ (Set.range (fun e : (s : Set E) => v e))) = _ at h
  rw [heq] at h
  simpa using h

omit [Fintype E] [FiniteDimensional ℝ V] in

lemma support_exchange (v : E → V) {s : Finset E}
    (hs : LinearIndepOn ℝ v s) {x : V} {l : E →₀ ℝ}
    (hl : l ∈ Finsupp.supported ℝ ℝ (s : Set E))
    (hx : Finsupp.linearCombination ℝ v l = x) {f : E} (hf : f ∈ l.support) :
    x ∉ span v (s.erase f) := by
  intro h
  obtain ⟨l', hl', hx'⟩ := (Finsupp.mem_span_image_iff_linearCombination ℝ).mp h
  have hl's : l' ∈ Finsupp.supported ℝ ℝ (s : Set E) := by
    rw [Finsupp.mem_supported] at hl' ⊢
    exact hl'.trans (Finset.erase_subset _ _)
  have heq : l = l' := (linearIndepOn_iffₛ.mp hs) l hl l' hl's (hx.trans hx'.symm)
  have hz : l' f = 0 := by
    apply Finsupp.notMem_support_iff.mp
    intro hmem
    have := ((Finsupp.mem_supported ℝ l').mp hl') hmem
    simp at this
  exact (Finsupp.mem_support_iff.mp hf) (heq ▸ hz)

omit [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [FiniteDimensional ℝ V] in
lemma valid_empty (v : E → V) : Valid v (fun _ : I => ∅) := by
  constructor
  · intro i; simp
  · intro i j h; simp

omit [Fintype E] [DecidableEq E] [FiniteDimensional ℝ V] in
lemma valid_update {v : E → V} (F : State v I) (i : I) (s : Finset E)
    (hs : LinearIndepOn ℝ v (s : Set E))
    (hd : ∀ j, j ≠ i → Disjoint s (F.1 j)) : Valid v (Function.update F.1 i s) := by
  constructor
  · intro j
    by_cases h : j = i
    · subst j; simpa using hs
    · simpa [Function.update_of_ne h] using F.2.1 j
  · intro j k hjk
    by_cases hj : j = i
    · subst j
      simpa [Function.update_of_ne (Ne.symm hjk)] using hd k (Ne.symm hjk)
    · by_cases hk : k = i
      · subst k
        simpa [Function.update_of_ne hj] using (hd j hj).symm
      · simpa [Function.update_of_ne hj, Function.update_of_ne hk] using F.2.2 hjk

omit [Fintype E] [DecidableEq I] [FiniteDimensional ℝ V] in
lemma disjoint_insert_unused {v : E → V} (F : State v I) {i : I} {s : Finset E}
    (hs : s ⊆ F.1 i) {e : E} (he : unused F e) :
    ∀ j, j ≠ i → Disjoint (insert e s) (F.1 j) := by
  intro j hj
  rw [Finset.disjoint_insert_left]
  exact ⟨he j, (F.2.2 (Ne.symm hj)).mono_left hs⟩

omit [Fintype E] [DecidableEq E] [FiniteDimensional ℝ V] in
lemma cost_update {v : E → V} (F : State v I) {i : I} {s : Finset E}
    (h : Valid v (Function.update F.1 i s)) :
    cost (⟨Function.update F.1 i s, h⟩ : State v I) + (F.1 i).card = cost F + s.card := by
  unfold cost
  have hsum := Finset.sum_update_of_mem (Finset.mem_univ i) (fun j => (F.1 j).card) s.card
  have heq : (fun j => ((Function.update F.1 i s) j).card) =
      Function.update (fun j => (F.1 j).card) i s.card := by
    ext j; by_cases hj : j = i <;> simp [hj, Function.update_of_ne]
  rw [heq]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add (Finset.univ : Finset I) _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  have he : ∑ j ∈ Finset.univ.erase i,
      Function.update (fun j => (F.1 j).card) i s.card j =
      ∑ j ∈ Finset.univ.erase i, (F.1 j).card := by
    apply Finset.sum_congr rfl
    intro j hj
    exact Function.update_of_ne (Finset.mem_erase.mp hj).1 _ _
  rw [he]
  omega

omit [DecidableEq E] [DecidableEq I] [FiniteDimensional ℝ V] in
lemma exists_maximal_state (v : E → V) :
    ∃ F : State v I, ∀ F' : State v I, cost F' ≤ cost F := by
  classical
  let : Fintype (State v I) := Fintype.ofFinite _
  have hne : (Finset.univ : Finset (State v I)).Nonempty :=
    ⟨⟨fun _ => ∅, valid_empty v⟩, Finset.mem_univ _⟩
  obtain ⟨F, _, hF⟩ := Finset.exists_max_image (Finset.univ : Finset (State v I)) cost hne
  exact ⟨F, fun F' => hF F' (Finset.mem_univ _)⟩

omit [Fintype E] [FiniteDimensional ℝ V] in
lemma maximal_unused_mem_span {v : E → V} {F : State v I}
    (hF : ∀ F' : State v I, cost F' ≤ cost F) {e : E} (he : unused F e) (i : I) :
    v e ∈ span v (F.1 i) := by
  by_contra h
  have hs : LinearIndepOn ℝ v (insert e (F.1 i) : Finset E) := by
    simpa only [Finset.coe_insert] using (F.2.1 i).insert h
  have hv := valid_update F i _ hs (disjoint_insert_unused F (Subset.refl _) he)
  have hc := cost_update F hv
  have hu := hF ⟨_, hv⟩
  rw [Finset.card_insert_of_notMem (he i)] at hc
  omega

omit [Fintype E] [FiniteDimensional ℝ V] in
lemma unused_after_exchange {v : E → V} {F F' : State v I} {i : I} {e f : E}
    (he : unused F e) (hf : f ∈ F.1 i)
    (h : F'.1 = Function.update F.1 i (insert e ((F.1 i).erase f))) : unused F' f := by
  intro j
  rw [h]
  by_cases hj : j = i
  · subst j
    have hfe : f ≠ e := by rintro rfl; exact he i hf
    simp [hfe]
  · rw [Function.update_of_ne hj]
    exact fun hfj => Finset.disjoint_left.mp (F.2.2 (Ne.symm hj)) hf hfj

omit [Fintype E] [FiniteDimensional ℝ V] in
lemma Move.cost_eq {v : E → V} {F F' : State v I} (h : Move F F') : cost F' = cost F := by
  obtain ⟨i, e, f, he, hf, heq⟩ := h
  have hv : Valid v (Function.update F.1 i (insert e ((F.1 i).erase f))) := heq ▸ F'.2
  have hc := cost_update F hv
  have hsame : (⟨_, hv⟩ : State v I) = F' := Subtype.ext heq.symm
  rw [hsame, Finset.card_insert_of_notMem (fun hh => he i (Finset.mem_erase.mp hh).2),
    Finset.card_erase_of_mem hf] at hc
  have hfpos := Finset.card_pos.mpr ⟨f, hf⟩
  omega

omit [Fintype E] [FiniteDimensional ℝ V] in
lemma reachable_cost_eq {v : E → V} {F F' : State v I}
    (h : Relation.ReflTransGen Move F F') : cost F' = cost F := by
  induction h with
  | refl => rfl
  | @tail F' F'' hr hm ih => exact hm.cost_eq.trans ih

omit [Fintype E] [FiniteDimensional ℝ V] in
lemma reachable_maximal {v : E → V} {F F' : State v I}
    (hF : ∀ G : State v I, cost G ≤ cost F)
    (h : Relation.ReflTransGen Move F F') : ∀ G : State v I, cost G ≤ cost F' := by
  intro G
  rw [reachable_cost_eq h]
  exact hF G

omit [FiniteDimensional ℝ V] in
lemma mem_recycled {v : E → V} {F : State v I} {e : E} :
    e ∈ recycled F ↔ ∃ F', Relation.ReflTransGen Move F F' ∧ unused F' e := by
  classical
  simp [recycled]

omit [FiniteDimensional ℝ V] in
lemma unused_span_recycled {v : E → V} {F F' : State v I}
    (hF : ∀ G : State v I, cost G ≤ cost F)
    (hr : Relation.ReflTransGen Move F F') {e : E} (he : unused F' e) (i : I) :
    v e ∈ span v (F'.1 i ∩ recycled F) := by
  have hsp := maximal_unused_mem_span (reachable_maximal hF hr) he i
  obtain ⟨l, hl, hle⟩ := (Finsupp.mem_span_image_iff_linearCombination ℝ).mp hsp
  apply (Finsupp.mem_span_image_iff_linearCombination ℝ).mpr
  refine ⟨l, ?_, hle⟩
  rw [Finsupp.mem_supported]
  intro f hf
  have hfi : f ∈ F'.1 i := (Finsupp.mem_supported ℝ l).mp hl hf
  refine Finset.mem_inter.mpr ⟨hfi, mem_recycled.mpr ?_⟩
  have hex := support_exchange v (F'.2.1 i) hl hle hf
  have hs : LinearIndepOn ℝ v (insert e ((F'.1 i).erase f) : Finset E) := by
    simpa only [Finset.coe_insert] using
      ((F'.2.1 i).mono (Finset.erase_subset _ _)).insert hex
  have hv := valid_update F' i _ hs
    (disjoint_insert_unused F' (Finset.erase_subset _ _) he)
  let F'' : State v I := ⟨_, hv⟩
  have hm : Move F' F'' := ⟨i, e, f, he, hfi, rfl⟩
  exact ⟨F'', hr.tail hm, unused_after_exchange he hfi rfl⟩

omit [FiniteDimensional ℝ V] in
lemma move_span_recycled_eq {v : E → V} {F F' F'' : State v I}
    (hF : ∀ G : State v I, cost G ≤ cost F)
    (hr : Relation.ReflTransGen Move F F') (hm : Move F' F'') (j : I) :
    span v (F''.1 j ∩ recycled F) = span v (F'.1 j ∩ recycled F) := by
  obtain ⟨i, e, f, he, hf, hup⟩ := hm
  by_cases hji : j = i
  · subst j
    have heU : v e ∈ span v (F'.1 i ∩ recycled F) := unused_span_recycled hF hr he i
    have hfU : v f ∈ span v (F''.1 i ∩ recycled F) :=
      unused_span_recycled hF (hr.tail ⟨i, e, f, he, hf, hup⟩)
        (unused_after_exchange he hf hup) i
    apply le_antisymm
    · apply (span_le_iff v).mpr
      intro g hg
      have hgU := (Finset.mem_inter.mp hg).2
      have hg' := (Finset.mem_inter.mp hg).1
      rw [hup, Function.update_self] at hg'
      rcases Finset.mem_insert.mp hg' with rfl | hg'
      · exact heU
      · exact mem_span_self v (Finset.mem_inter.mpr ⟨(Finset.mem_erase.mp hg').2, hgU⟩)
    · apply (span_le_iff v).mpr
      intro g hg
      by_cases hgf : g = f
      · subst g; exact hfU
      · apply mem_span_self v
        apply Finset.mem_inter.mpr
        refine ⟨?_, (Finset.mem_inter.mp hg).2⟩
        rw [hup, Function.update_self]
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hgf, (Finset.mem_inter.mp hg).1⟩)
  · rw [hup, Function.update_of_ne hji]

omit [FiniteDimensional ℝ V] in
lemma reachable_span_recycled_eq {v : E → V} {F F' : State v I}
    (hF : ∀ G : State v I, cost G ≤ cost F)
    (hr : Relation.ReflTransGen Move F F') (i : I) :
    span v (F'.1 i ∩ recycled F) = span v (F.1 i ∩ recycled F) := by
  induction hr with
  | refl => rfl
  | @tail F' F'' hr hm ih => exact (move_span_recycled_eq hF hr hm i).trans ih

omit [FiniteDimensional ℝ V] in

lemma span_recycled_eq {v : E → V} {F : State v I}
    (hF : ∀ G : State v I, cost G ≤ cost F) (i : I) :
    span v (recycled F) = span v (F.1 i ∩ recycled F) := by
  apply le_antisymm
  · apply (span_le_iff v).mpr
    intro e he
    obtain ⟨F', hr, he'⟩ := mem_recycled.mp he
    rw [← reachable_span_recycled_eq hF hr i]
    exact unused_span_recycled hF hr he' i
  · exact span_mono v Finset.inter_subset_right

omit [FiniteDimensional ℝ V] in
lemma cost_decomposition {v : E → V} {F : State v I}
    (hF : ∀ G : State v I, cost G ≤ cost F) :
    cost F = (Finset.univ \ recycled F).card +
      Fintype.card I * Module.finrank ℝ (span v (recycled F)) := by
  classical
  have hcover : Finset.univ \ recycled F =
      Finset.univ.biUnion (fun i => F.1 i \ recycled F) := by
    ext e
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · intro he
      have hused : ∃ i, e ∈ F.1 i := by
        by_contra h
        have hu : unused F e := by simpa only [unused, not_exists] using h
        exact he (mem_recycled.mpr ⟨F, Relation.ReflTransGen.refl, hu⟩)
      obtain ⟨i, hi⟩ := hused
      exact ⟨i, hi, he⟩
    · rintro ⟨i, hi, he⟩; exact he
  have hdisj : (↑(Finset.univ : Finset I) : Set I).PairwiseDisjoint
      (fun i => F.1 i \ recycled F) := by
    intro i _ j _ hij
    exact (F.2.2 hij).mono Finset.sdiff_subset Finset.sdiff_subset
  have hrank (i : I) : (F.1 i ∩ recycled F).card =
      Module.finrank ℝ (span v (recycled F)) := by
    rw [span_recycled_eq hF i]
    exact (indep_rank v ((F.2.1 i).mono Finset.inter_subset_left)).symm
  rw [hcover, Finset.card_biUnion hdisj]
  calc
    cost F = ∑ i, ((F.1 i \ recycled F).card + (F.1 i ∩ recycled F).card) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (Finset.card_sdiff_add_card_inter _ _).symm
    _ = (∑ i, (F.1 i \ recycled F).card) +
        Fintype.card I * Module.finrank ℝ (span v (recycled F)) := by
      simp_rw [hrank, Finset.sum_add_distrib]
      simp

theorem vector_base_packing (v : E → V)
    (hcut : ∀ U : Finset E,
      Fintype.card I * Module.finrank ℝ (span v Finset.univ) ≤
        (Finset.univ \ U).card + Fintype.card I * Module.finrank ℝ (span v U)) :
    ∃ F : State v I, ∀ i, span v (F.1 i) = span v Finset.univ := by
  obtain ⟨F, hF⟩ := exists_maximal_state (I := I) v
  have hle (i : I) : (F.1 i).card ≤ Module.finrank ℝ (span v Finset.univ) := by
    rw [← indep_rank v (F.2.1 i)]
    exact Submodule.finrank_mono (span_mono v (Finset.subset_univ _))
  have htotal : cost F = Fintype.card I * Module.finrank ℝ (span v Finset.univ) := by
    apply le_antisymm
    · calc
        cost F ≤ ∑ _i : I, Module.finrank ℝ (span v Finset.univ) :=
          Finset.sum_le_sum fun i _ => hle i
        _ = _ := by simp
    · rw [cost_decomposition hF]
      exact hcut (recycled F)
  have hcards (i : I) : (F.1 i).card = Module.finrank ℝ (span v Finset.univ) := by
    apply (Finset.sum_eq_sum_iff_of_le (fun i (_ : i ∈ (Finset.univ : Finset I)) => hle i)).mp ?_ i
      (Finset.mem_univ i)
    simpa [cost] using htotal
  refine ⟨F, fun i => ?_⟩
  apply Submodule.eq_of_le_of_finrank_eq (span_mono v (Finset.subset_univ _))
  rw [indep_rank v (F.2.1 i), hcards]

omit [Fintype E] [FiniteDimensional ℝ V] in
lemma masked_span (v : E → V) (T U : Finset E) :
    span (fun e => if e ∈ T then v e else 0) U = span v (U ∩ T) := by
  classical
  apply le_antisymm
  · apply (span_le_iff _).mpr
    intro e he
    by_cases heT : e ∈ T
    · simp only [ite_eq_left heT]
      exact mem_span_self v (Finset.mem_inter.mpr ⟨he, heT⟩)
    · simp [heT]
  · apply (span_le_iff _).mpr
    intro e he
    have hm := mem_span_self (fun e => if e ∈ T then v e else 0) (Finset.mem_inter.mp he).1
    simpa only [ite_eq_left (Finset.mem_inter.mp he).2] using hm

theorem vector_base_packing_on (v : E → V) (T : Finset E)
    (hcut : ∀ U : Finset E, U ⊆ T →
      Fintype.card I * Module.finrank ℝ (span v T) ≤
        (T \ U).card + Fintype.card I * Module.finrank ℝ (span v U)) :
    ∃ F : I → Finset E, Valid v F ∧ ∀ i, F i ⊆ T ∧ span v (F i) = span v T := by
  classical
  let w : E → V := fun e => if e ∈ T then v e else 0
  have hcrit : ∀ U : Finset E, Fintype.card I * Module.finrank ℝ (span w Finset.univ) ≤
      (Finset.univ \ U).card + Fintype.card I * Module.finrank ℝ (span w U) := by
    intro U
    have hw (A : Finset E) : span w A = span v (A ∩ T) := masked_span v T A
    rw [hw, hw, Finset.univ_inter]
    have h := hcut (U ∩ T) Finset.inter_subset_right
    apply h.trans
    apply Nat.add_le_add_right
    apply Finset.card_le_card
    intro e he
    simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_univ, true_and] at he ⊢
    tauto
  obtain ⟨F, hF⟩ := vector_base_packing (I := I) w hcrit
  have hsub (i : I) : F.1 i ⊆ T := by
    intro e he
    have hz := (F.2.1 i).ne_zero he
    by_contra h
    exact hz (by simp [w, h])
  refine ⟨F.1, ⟨?_, F.2.2⟩, fun i => ⟨hsub i, ?_⟩⟩
  · intro i
    apply (F.2.1 i).congr
    intro e he
    simp [w, hsub i he]
  · have heq := hF i
    simpa only [w, masked_span, Finset.inter_eq_left.mpr (hsub i), Finset.univ_inter] using heq

end StrongThinTree.Packing

namespace StrongThinTree.MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)

lemma rep_same (T : Finset (Fin m)) (u : Fin n) : G.Same T (G.rep T u) u :=
  Quotient.mk_out (s := G.components T) u

lemma rep_eq_iff (T : Finset (Fin m)) (u v : Fin n) : G.rep T u = G.rep T v ↔ G.Same T u v := by
  constructor
  · intro h
    exact G.same_trans (G.same_symm (G.rep_same T u)) (h ▸ G.rep_same T v)
  · intro h
    exact congrArg Quotient.out (Quotient.sound h)

lemma rep_idempotent (T : Finset (Fin m)) (u : Fin n) : G.rep T (G.rep T u) = G.rep T u :=
  (G.rep_eq_iff T _ _).mpr (G.rep_same T u)

lemma rep_endpoints {T : Finset (Fin m)} {e : Fin m} (he : e ∈ T) :
    G.rep T (G.left e) = G.rep T (G.right e) :=
  (G.rep_eq_iff T _ _).mpr (G.same_endpoints he)

lemma repDifference_mem (T : Finset (Fin m)) (u : Fin n) : G.repDifference T u ∈ G.edgeSpan T :=
  G.same_symm (G.rep_same T u)

lemma repDifference_independent (T : Finset (Fin m)) :
    LinearIndependent ℝ (fun u : {u : Fin n // G.rep T u ≠ u} => G.repDifference T u) := by
  apply LinearIndependent.of_pairwise_dual_eq_zero_one _ (fun u => LinearMap.proj u.1)
  · intro u v huv
    have huv' : u.1 ≠ v.1 := fun h => huv (Subtype.ext h)
    have hru : u.1 ≠ G.rep T v.1 := by
      intro h
      have := G.rep_idempotent T v.1
      rw [← h] at this
      exact u.2 this
    simp [repDifference, point, huv', hru]
  · intro u
    simp [repDifference, point, (Ne.symm u.2)]

lemma edgeSpan_eq_repSpan (T : Finset (Fin m)) :
    G.edgeSpan T = Submodule.span ℝ
      (Set.range (fun u : {u : Fin n // G.rep T u ≠ u} => G.repDifference T u)) := by
  classical
  apply le_antisymm
  · apply (Packing.span_le_iff G.incidence).mpr
    intro e he
    have hdiff (u : Fin n) : G.repDifference T u ∈ Submodule.span ℝ
        (Set.range (fun u : {u : Fin n // G.rep T u ≠ u} => G.repDifference T u)) := by
      by_cases hu : G.rep T u = u
      · simp [repDifference, hu]
      · exact Submodule.subset_span ⟨⟨u, hu⟩, rfl⟩
    have h := (Submodule.span ℝ _).sub_mem (hdiff (G.left e)) (hdiff (G.right e))
    have heq : G.repDifference T (G.left e) - G.repDifference T (G.right e) = G.incidence e := by
      dsimp [repDifference, incidence]
      rw [G.rep_endpoints he]
      abel
    rwa [heq] at h
  · apply Submodule.span_le.mpr
    rintro x ⟨u, rfl⟩
    exact G.repDifference_mem T u

theorem incidence_rank (T : Finset (Fin m)) :
    Module.finrank ℝ (G.edgeSpan T) = n - G.componentCount T := by
  classical
  rw [G.edgeSpan_eq_repSpan, finrank_span_eq_card (G.repDifference_independent T),
    Fintype.card_subtype_compl]
  have heq : Finset.univ.image (G.rep T) = Finset.univ.filter (fun u => G.rep T u = u) := by
    ext u
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨v, rfl⟩
      exact G.rep_idempotent T v
    · intro hu
      exact ⟨u, hu⟩
  simp only [componentCount, heq, Fintype.card_fin, Fintype.card_subtype]

lemma connected_of_span_eq {T U : Finset (Fin m)}
    (h : G.edgeSpan T = G.edgeSpan U) (hT : G.Connected T) : G.Connected U := by
  rw [G.connected_iff_same] at hT ⊢
  intro u v
  change point u - point v ∈ G.edgeSpan U
  rw [← h]
  exact hT u v

theorem spanningTree_iff_independent (T : Finset (Fin m)) :
    G.SpanningTree T ↔ G.Connected T ∧ LinearIndepOn ℝ G.incidence (T : Set (Fin m)) := by
  constructor
  · rintro ⟨hconn, hmin⟩
    refine ⟨hconn, linearIndepOn_iff_notMem_span.mpr ?_⟩
    intro e he hdep
    have hd : G.incidence e ∈ G.edgeSpan (T.erase e) := by
      simpa only [edgeSpan, Packing.span, Finset.coe_erase] using hdep
    have heq : G.edgeSpan T = G.edgeSpan (T.erase e) := by
      calc
        G.edgeSpan T = G.edgeSpan (insert e (T.erase e)) := by rw [Finset.insert_erase he]
        _ = G.edgeSpan (T.erase e) := by
          change Packing.span G.incidence (insert e (T.erase e)) = _
          rw [Packing.span_insert, Submodule.span_insert_eq_span hd]
    exact hmin e he (G.connected_of_span_eq heq hconn)
  · rintro ⟨hconn, hind⟩
    refine ⟨hconn, fun e he hdel => ?_⟩
    have hnot := linearIndepOn_iff_notMem_span.mp hind e he
    apply hnot
    have hsame := (G.connected_iff_same (T.erase e)).mp hdel (G.left e) (G.right e)
    simpa only [Same, incidence, edgeSpan, Packing.span, Finset.coe_erase] using hsame

lemma componentCount_pos (hn : 0 < n) (T : Finset (Fin m)) : 0 < G.componentCount T := by
  apply Finset.card_pos.mpr
  exact ⟨G.rep T ⟨0, hn⟩, Finset.mem_image.mpr ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩⟩

lemma connected_componentCount {T : Finset (Fin m)} (hn : 0 < n) (hc : G.Connected T) :
    G.componentCount T = 1 := by
  apply Finset.card_eq_one.mpr
  let u : Fin n := ⟨0, hn⟩
  refine ⟨G.rep T u, ?_⟩
  ext v
  constructor
  · intro hv
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_singleton.mpr ((G.rep_eq_iff T w u).mpr ((G.connected_iff_same T).mp hc w u))
  · intro hv
    have hv' := Finset.mem_singleton.mp hv
    subst v
    exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩

lemma connected_rank {T : Finset (Fin m)} (hn : 0 < n) (hc : G.Connected T) :
    Module.finrank ℝ (G.edgeSpan T) = n - 1 := by
  rw [G.incidence_rank, G.connected_componentCount hn hc]

lemma spanningTree_card {T : Finset (Fin m)} (hn : 0 < n) (hT : G.SpanningTree T) : T.card = n - 1 := by
  rw [← Packing.indep_rank G.incidence ((G.spanningTree_iff_independent T).mp hT).2]
  exact G.connected_rank hn hT.1

lemma connected_of_componentCount_eq_one {T : Finset (Fin m)}
    (hc : G.componentCount T = 1) : G.Connected T := by
  rw [G.connected_iff_same]
  have ⟨v, hv⟩ := Finset.card_eq_one.mp hc
  intro a b
  have ha : G.rep T a ∈ Finset.univ.image (G.rep T) :=
    Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  have hb : G.rep T b ∈ Finset.univ.image (G.rep T) :=
    Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩
  rw [hv, Finset.mem_singleton] at ha hb
  exact (G.rep_eq_iff T a b).mp (ha.trans hb.symm)

end StrongThinTree.MultiGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_PartitionRank
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.Partitions.mem_crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uI uV uE2 uV2

section

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset Submodule
variable {n m : ℕ} (G : MultiGraph n m)

lemma connectedOn_mono_span {A : Finset (Fin n)} {F T : Finset (Fin m)}
    (h : G.edgeSpan F ≤ G.edgeSpan T) (hc : G.ConnectedOn A F) : G.ConnectedOn A T := by
  intro u hu v hv
  exact h (hc u hu v hv)

lemma independent_spanning_subset (F : Finset (Fin m)) :
    ∃ T ⊆ F, LinearIndepOn ℝ G.incidence (T : Set (Fin m)) ∧ G.edgeSpan T = G.edgeSpan F := by
  classical
  let h : LinearIndepOn ℝ G.incidence (∅ : Set (Fin m)) := linearIndepOn_empty ℝ G.incidence
  let U := h.extend (Set.empty_subset (F : Set (Fin m)))
  refine ⟨U.toFinset, ?_, ?_, ?_⟩
  · intro e he
    exact h.extend_subset (Set.empty_subset (F : Set (Fin m))) (Set.mem_toFinset.mp he)
  · simpa only [Set.coe_toFinset] using h.linearIndepOn_extend (Set.empty_subset (F : Set (Fin m)))
  · simpa only [edgeSpan, Packing.span, Set.coe_toFinset] using
      h.span_image_extend_eq_span_image (Set.empty_subset (F : Set (Fin m)))

lemma packableOn_iff_trees (F : Finset (Fin m)) (q : ℕ) (A : Finset (Fin n)) :
    G.PackableOn F q A ↔ ∃ T : Fin q → Finset (Fin m),
      (∀ i, T i ⊆ F ∧ G.TreeOn A (T i)) ∧
      ∀ ⦃i j⦄, i ≠ j → Disjoint (T i) (T j) := by
  classical
  constructor
  · rintro ⟨T, hT, hd⟩
    choose U hU hi hs using fun i => G.independent_spanning_subset (T i)
    refine ⟨U, fun i => ⟨?_, ?_, ?_, hi i⟩, fun i j hij =>
      disjoint_of_subset_left (hU i) (disjoint_of_subset_right (hU j) (hd hij))⟩
    · exact (hU i).trans ((hT i).1.trans (filter_subset _ _))
    · intro e he
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp ((hT i).1 (hU i he))).2⟩
    · exact G.connectedOn_mono_span (le_of_eq (hs i).symm) (hT i).2
  · rintro ⟨T, hT, hd⟩
    refine ⟨T, fun i => ⟨?_, (hT i).2.2.1⟩, hd⟩
    intro e he
    exact mem_filter.mpr ⟨(hT i).1 he, (mem_filter.mp ((hT i).2.1 he)).2⟩

lemma connectedOn_univ (T : Finset (Fin m)) : G.ConnectedOn univ T ↔ G.Connected T := by
  rw [G.connected_iff_same]
  simp only [ConnectedOn, mem_univ, forall_const]

lemma packableOn_univ (F : Finset (Fin m)) (q : ℕ) :
    G.PackableOn F q univ ↔ G.TreePackable F q := by
  rw [G.packableOn_iff_trees]
  constructor
  · rintro ⟨T, hT, hd⟩
    refine ⟨T, fun i => ⟨(hT i).1, ?_⟩, hd⟩
    exact (G.spanningTree_iff_independent _).mpr
      ⟨(G.connectedOn_univ _).mp (hT i).2.2.1, (hT i).2.2.2⟩
  · rintro ⟨T, hT, hd⟩
    refine ⟨T, fun i => ⟨(hT i).1, ?_, ?_, ?_⟩, hd⟩
    · simp [internal]
    · exact (G.connectedOn_univ _).mpr (hT i).2.1
    · exact ((G.spanningTree_iff_independent _).mp (hT i).2).2

end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_PartitionHierarchy
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
open Finset
variable {n m : ℕ} (G : MultiGraph n m)

lemma connectedOn_cut {A S : Finset (Fin n)} {T : Finset (Fin m)}
    (hc : G.ConnectedOn A T) (hS : S.Nonempty) (hSA : S ⊂ A) : (G.cut T S).Nonempty := by
  classical
  by_contra hcut
  have hempty : G.cut T S=∅ := not_nonempty_iff_eq_empty.mp hcut
  let f : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑u ∈ S, LinearMap.proj u
  have hker : G.edgeSpan T ≤ LinearMap.ker f := by
    apply (Packing.span_le_iff G.incidence).mpr
    intro e he
    have hiff : G.left e ∈ S ↔ G.right e ∈ S := by
      have hh : ¬((G.left e ∈ S ∧ G.right e ∉ S) ∨ (G.right e ∈ S ∧ G.left e ∉ S)) := by
        intro h
        have hm : e ∈ G.cut T S := mem_filter.mpr ⟨he,h⟩
        simp [hempty] at hm
      tauto
    change f (G.incidence e)=0
    rw [incidence,map_sub]
    change (∑u ∈ S, LinearMap.proj u : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point (G.left e)) -
      (∑u ∈ S, LinearMap.proj u : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point (G.right e))=0
    simp only [sumOn_point,hiff,sub_self]
  obtain ⟨u,hu⟩ := hS
  have hv : (A \ S).Nonempty := sdiff_nonempty.mpr (not_subset.mpr (by
    by_contra h
    push Not at h
    exact (not_ssubset_of_subset h) hSA))
  obtain ⟨v,hv⟩ := hv
  obtain ⟨hvA,hvS⟩ := mem_sdiff.mp hv
  have hz := hker (hc u (hSA.subset hu) v hvA)
  change f (point u-point v)=0 at hz
  rw [map_sub] at hz
  change (∑w ∈ S, LinearMap.proj w : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point u) -
    (∑w ∈ S, LinearMap.proj w : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point v)=0 at hz
  simp [sumOn_point,hu,hvS] at hz

lemma packableOn_edgeConnectedReal {F : Finset (Fin m)} {q : ℕ} {A : Finset (Fin n)}
    (hp : G.PackableOn F q A) : G.EdgeConnectedReal A q := by
  classical
  obtain ⟨T,hT,hd⟩ := hp
  intro S hS hSA
  have hne (i : Fin q) := G.connectedOn_cut (hT i).2 hS hSA
  have hdis : (↑(univ : Finset (Fin q)) : Set (Fin q)).PairwiseDisjoint (fun i => G.cut (T i) S) := by
    intro i _ j _ hij
    exact disjoint_of_subset_left (filter_subset _ _) (disjoint_of_subset_right (filter_subset _ _) (hd hij))
  have hsub : univ.biUnion (fun i : Fin q => G.cut (T i) S) ⊆ G.cut (G.inducedEdges A) S := by
    apply biUnion_subset.mpr
    intro i _ e he
    obtain ⟨het,hes⟩ := mem_filter.mp he
    have hh := (mem_filter.mp ((hT i).1 het)).2
    exact mem_filter.mpr ⟨(G.mem_inducedEdges A e).mpr hh,hes⟩
  have hh := card_le_card hsub
  rw [card_biUnion hdis] at hh
  have hl : q ≤ ∑i : Fin q, (G.cut (T i) S).card := by
    simpa using sum_le_sum (s := (univ : Finset (Fin q))) (f := fun _ => 1)
      (g := fun i => (G.cut (T i) S).card) (fun i _ => card_pos.mpr (hne i))
  exact_mod_cast hl.trans hh

end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_ExtractionCriterion
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.Partitions.mem_crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Finset Matrix
open scoped MatrixOrder
namespace StrongThinTree.MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)
lemma treePackable_edgeConnected {r : ℕ} (hp : G.TreePackable univ r) : G.EdgeConnected r := by
  have hh := G.packableOn_edgeConnectedReal ((G.packableOn_univ univ r).mpr hp)
  intro S hS hS'
  have hs : S ⊂ (univ : Finset (Fin n)) := Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _,hS'⟩
  have hc := hh S hS hs
  have hi : G.inducedEdges univ = univ := by ext e; simp [mem_inducedEdges]
  rw [hi] at hc
  exact_mod_cast hc

end StrongThinTree.MultiGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_TwoSystems
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uD uE

section

noncomputable section
open Matrix Finset
open scoped MatrixOrder
namespace StrongThinTree
variable {I : Type uI} {D : Type uD} {E : Type uE} [Fintype I] [Fintype D] [Fintype E]
  [DecidableEq I] [DecidableEq D] [DecidableEq E]

omit [Fintype I] [DecidableEq I] [DecidableEq D] [Fintype E] [DecidableEq E] in
lemma qform_covariance (v : I → D → ℝ) (A : Finset I) (x : D → ℝ) :
    qform (∑i ∈ A, vecMulVec (v i) (v i)) x=∑i ∈ A, (x ⬝ᵥ v i)^2 := by
  simp only [qform,sum_mulVec,dotProduct_sum]
  apply sum_congr rfl
  intro i _
  rw [vecMulVec_mulVec,dotProduct_smul,dotProduct_comm (v i) x]
  simp [pow_two]

end StrongThinTree

end
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Representation
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Hermitian.instFiniteDimensionalRealSubtypeMatMemSubmoduleH
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.Partitions.mem_crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι uE uT uI uE2 uE3 uV uE4 uV2 uW

section

open Matrix Finset
open scoped BigOperators MatrixOrder Matrix.Norms.Elementwise
namespace StrongThinTree
noncomputable section

section Determinant
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma one_le_det_one_add {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    1 ≤ (1 + A).det := by
  let U := hA.isHermitian.eigenvectorUnitary
  let D : Matrix ι ι ℝ := Matrix.diagonal hA.isHermitian.eigenvalues
  have hspec : A = (U : Matrix ι ι ℝ) * D * star (U : Matrix ι ι ℝ) := by
    simpa [D, U, Unitary.conjStarAlgAut_apply] using hA.isHermitian.spectral_theorem
  have hconj : 1 + A = (U : Matrix ι ι ℝ) * (1 + D) * star (U : Matrix ι ι ℝ) := by
    rw [hspec]
    simp [mul_add, add_mul]
  rw [hconj, Matrix.det_mul_comm, ← mul_assoc, Unitary.coe_star_mul_self, one_mul]
  have hdiag : 1 + D = Matrix.diagonal (fun i => 1 + hA.isHermitian.eigenvalues i) := by
    simp only [D, ← Matrix.diagonal_one, Matrix.diagonal_add]
  rw [hdiag, Matrix.det_diagonal]
  exact Finset.one_le_prod (fun i _ => by linarith [hA.eigenvalues_nonneg i])

lemma posDef_sqrt_factors {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    ∃ S : Matrix ι ι ℝ, S.IsHermitian ∧ IsUnit S ∧ S * S = A := by
  refine ⟨CFC.sqrt A, (CFC.sqrt_nonneg A).posSemidef.isHermitian, ?_,
    CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg⟩
  apply (isUnit_pow_iff (by decide : 2 ≠ 0)).mp
  rw [CFC.sq_sqrt A hA.posSemidef.nonneg]
  exact hA.isUnit

lemma det_le_det_add_of_posSemidef {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosSemidef) : A.det ≤ (A + B).det := by
  obtain ⟨S, hSH, hSU, hS⟩ := posDef_sqrt_factors hA
  have hSi : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S
    ((Matrix.isUnit_iff_isUnit_det S).mp hSU)
  have hiS : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S
    ((Matrix.isUnit_iff_isUnit_det S).mp hSU)
  let Q := S⁻¹ * B * S⁻¹
  have hQ : Q.PosSemidef := by
    simpa only [hSH.inv.eq] using hB.mul_mul_conjTranspose_same S⁻¹
  have hdecomp : A + B = S * (1 + Q) * S := by
    dsimp [Q]
    simp only [mul_add, add_mul, mul_one, ← mul_assoc, hS]
    simp only [mul_assoc, hSi, hiS, one_mul, mul_one]
  have hdetS : S.det * S.det = A.det := by rw [← Matrix.det_mul, hS]
  have hdet : (A + B).det = A.det * (1 + Q).det := by
    rw [hdecomp, Matrix.det_mul, Matrix.det_mul]
    rw [← hdetS]
    ring
  rw [hdet]
  exact le_mul_of_one_le_right hA.det_pos.le (one_le_det_one_add hQ)

end Determinant
section Covariance
variable {T : Type uT} {I : Type uI} [Fintype T] [DecidableEq T] [Nonempty T]
  [Fintype I] [DecidableEq I]

lemma basisCov_eq_sum (b : Matrix I I ℝ) (a : I → ℝ) :
    basisCov b a = ∑ j, Real.exp (a j) • vecMulVec (fun i => b i j) (fun i => b i j) := by
  apply Matrix.ext
  intro k l
  change (∑ j, (b * diagonal (fun j => Real.exp (a j))) k j * b l j) = _
  simp only [Matrix.mul_diagonal, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.vecMulVec_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq T] [Nonempty T] in
lemma packingCov_eq_sum (b : T → Matrix I I ℝ) (a : EuclideanSpace ℝ (T × I)) :
    packingCov b a = ∑ e : T × I, Real.exp (a e) •
      vecMulVec (fun i => b e.1 i e.2) (fun i => b e.1 i e.2) := by
  simp only [packingCov, basisCov_eq_sum, Fintype.sum_prod_type]

lemma basisCov_posDef (b : Matrix I I ℝ) (hb : IsUnit b) (a : I → ℝ) :
    (basisCov b a).PosDef := by
  have hd : (diagonal (fun j => Real.exp (a j))).PosDef :=
    Matrix.PosDef.diagonal (fun j => Real.exp_pos _)
  simpa [basisCov] using hd.mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_of_isUnit hb)

omit [DecidableEq T] in
lemma packingCov_posDef (b : T → Matrix I I ℝ) (hb : ∀ t, IsUnit (b t))
    (a : EuclideanSpace ℝ (T × I)) : (packingCov b a).PosDef := by
  exact Matrix.posDef_sum Finset.univ_nonempty
    (fun t _ => basisCov_posDef (b t) (hb t) _)

lemma det_basisCov (b : Matrix I I ℝ) (a : I → ℝ) :
    (basisCov b a).det = b.det ^ 2 * Real.exp (∑ j, a j) := by
  simp only [basisCov, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  rw [Real.exp_sum]
  ring

omit [Nonempty T] in
lemma det_basisCov_le_packingCov (b : T → Matrix I I ℝ)
    (hb : ∀ t, IsUnit (b t)) (a : EuclideanSpace ℝ (T × I)) (t : T) :
    (basisCov (b t) (fun j => a (t, j))).det ≤ (packingCov b a).det := by
  have hsum : packingCov b a = basisCov (b t) (fun j => a (t, j)) +
      ∑ u ∈ Finset.univ.erase t, basisCov (b u) (fun j => a (u, j)) := by
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ t)).symm
  rw [hsum]
  apply det_le_det_add_of_posSemidef (basisCov_posDef _ (hb t) _)
  exact Matrix.posSemidef_sum _ (fun u _ => (basisCov_posDef _ (hb u) _).posSemidef)

lemma packingObjective_bddBelow (b : T → Matrix I I ℝ) (hb : ∀ t, IsUnit (b t)) :
    ∀ a, (∑ t, Real.log ((b t).det ^ 2)) / Fintype.card T ≤ packingObjective b a := by
  intro a
  have ht (t : T) : Real.log ((b t).det ^ 2) + ∑ j, a (t, j) ≤
      Real.log (packingCov b a).det := by
    have hd := (basisCov_posDef (b t) (hb t) (fun j => a (t, j))).det_pos
    have hbd := det_basisCov_le_packingCov b hb a t
    have he := Real.log_le_log hd hbd
    rw [det_basisCov, Real.log_mul (by
      have := (Matrix.isUnit_iff_isUnit_det _).mp (hb t)
      exact pow_ne_zero 2 this.ne_zero) (ne_of_gt (Real.exp_pos _)), Real.log_exp] at he
    exact he
  have hs := Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) => ht t)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  have hq : (0 : ℝ) < Fintype.card T := Nat.cast_pos.mpr Fintype.card_pos
  dsimp [packingObjective]
  rw [le_sub_iff_add_le, ← add_div, div_le_iff₀ hq]
  rw [mul_comm] at hs
  simpa only [Fintype.sum_prod_type] using hs

end Covariance

end
end StrongThinTree

namespace StrongThinTree.Packing
noncomputable section
open scoped BigOperators
open Finset
variable {E : Type uE3} {V : Type uV} [Fintype E] [DecidableEq E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

omit [Fintype E] in

lemma projected_trace_bound (v : E → V) (A U : Finset E) {c h : ℝ}
    (_hU : U ⊆ A) (hn : ∀ e ∈ A, ‖v e‖ ^ 2 ≤ h)
    (hlow : ∀ x : V, c * ‖x‖ ^ 2 ≤ ∑ e ∈ A, (inner ℝ x (v e)) ^ 2) :
    c * (Module.finrank ℝ V - Module.finrank ℝ (span v U) : ℕ) ≤
      h * (A \ U).card := by
  classical
  let W := span v U
  let b := stdOrthonormalBasis ℝ Wᗮ
  let w := fun i : Fin (Module.finrank ℝ Wᗮ) => (b i : V)
  have hw : Orthonormal ℝ w := by
    rw [orthonormal_iff_ite]
    intro i j
    exact (orthonormal_iff_ite.mp b.orthonormal) i j
  have hzero (i : Fin (Module.finrank ℝ Wᗮ)) (e : E) (he : e ∈ U) :
      inner ℝ (w i) (v e) = 0 :=
    Submodule.inner_left_of_mem_orthogonal (mem_span_self v he) (b i).2
  have hlow' (i : Fin (Module.finrank ℝ Wᗮ)) :
      c ≤ ∑ e ∈ A \ U, (inner ℝ (w i) (v e)) ^ 2 := by
    have hi := hlow (w i)
    rw [hw.norm_eq_one, one_pow, mul_one] at hi
    have heq : ∑ e ∈ A \ U, (inner ℝ (w i) (v e)) ^ 2 =
        ∑ e ∈ A, (inner ℝ (w i) (v e)) ^ 2 := by
      apply Finset.sum_subset Finset.sdiff_subset
      intro e he hne
      have heU : e ∈ U := by simpa [he] using hne
      simp [hzero i e heU]
    rwa [heq]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i hi => hlow' i)
  have hsb : (∑ i : Fin (Module.finrank ℝ Wᗮ), ∑ e ∈ A \ U,
      (inner ℝ (w i) (v e)) ^ 2) ≤ ∑ e ∈ A \ U, h := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro e he
    have hb := hw.sum_inner_products_le (s := Finset.univ) (v e)
    simp only [Real.norm_eq_abs, sq_abs] at hb
    exact hb.trans (hn e (Finset.mem_sdiff.mp he).1)
  have ht := hs.trans hsb
  have hdim := W.finrank_add_finrank_orthogonal
  have heq : Module.finrank ℝ Wᗮ = Module.finrank ℝ V - Module.finrank ℝ W := by omega
  simpa [heq, mul_comm, W] using ht

omit [Fintype E] in
lemma lower_frame_span (v : E → V) (A : Finset E) {c h : ℝ} (hc : 0 < c)
    (hn : ∀ e ∈ A, ‖v e‖ ^ 2 ≤ h)
    (hlow : ∀ x : V, c * ‖x‖ ^ 2 ≤ ∑ e ∈ A, (inner ℝ x (v e)) ^ 2) :
    span v A = ⊤ := by
  have hb := projected_trace_bound v A A (Subset.refl _) hn hlow
  simp only [Finset.sdiff_self, Finset.card_empty, Nat.cast_zero, mul_zero] at hb
  have hzero : (Module.finrank ℝ V - Module.finrank ℝ (span v A) : ℕ) = 0 := by
    have hh : ((Module.finrank ℝ V - Module.finrank ℝ (span v A) : ℕ) : ℝ) ≤ 0 :=
      by nlinarith
    exact_mod_cast (le_antisymm hh (Nat.cast_nonneg _))
  apply Submodule.eq_top_of_finrank_eq
  have hle := (span v A).finrank_le
  omega

theorem projected_trace_base_packing (v : E → V) (A : Finset E)
    {r : ℕ} {c h : ℝ} (hc : 0 < c) (hh : 0 < h) (hr : (r : ℝ) * h ≤ c)
    (hn : ∀ e ∈ A, ‖v e‖ ^ 2 ≤ h)
    (hlow : ∀ x : V, c * ‖x‖ ^ 2 ≤ ∑ e ∈ A, (inner ℝ x (v e)) ^ 2) :
    ∃ F : Fin r → Finset E, Valid v F ∧
      ∀ i, F i ⊆ A ∧ span v (F i) = ⊤ := by
  have htop := lower_frame_span v A hc hn hlow
  have hp : ∀ U : Finset E, U ⊆ A →
      Fintype.card (Fin r) * Module.finrank ℝ (span v A) ≤
        (A \ U).card + Fintype.card (Fin r) * Module.finrank ℝ (span v U) := by
    intro U hU
    have ht := projected_trace_bound v A U hU hn hlow
    have hdim := (span v U).finrank_le
    have hdiff : (r : ℝ) * (Module.finrank ℝ V - Module.finrank ℝ (span v U) : ℕ) ≤
        (A \ U).card := by
      have h₁ := mul_le_mul_of_nonneg_right hr
        (Nat.cast_nonneg (Module.finrank ℝ V - Module.finrank ℝ (span v U)))
      have h₂ : h * ((r : ℝ) * (Module.finrank ℝ V - Module.finrank ℝ (span v U) : ℕ)) ≤
          h * (A \ U).card := by nlinarith [h₁.trans ht]
      exact (mul_le_mul_iff_right₀ hh).mp h₂
    have hdiffN : r * (Module.finrank ℝ V - Module.finrank ℝ (span v U)) ≤
        (A \ U).card := by exact_mod_cast hdiff
    rw [htop, finrank_top, Fintype.card_fin]
    have heq : Module.finrank ℝ V =
        (Module.finrank ℝ V - Module.finrank ℝ (span v U)) + Module.finrank ℝ (span v U) := by omega
    rw [heq, Nat.mul_add]
    exact Nat.add_le_add_right hdiffN _
  obtain ⟨F, hF, hs⟩ := vector_base_packing_on v A hp
  exact ⟨F, hF, fun i => ⟨(hs i).1, (hs i).2.trans htop⟩⟩

end
end StrongThinTree.Packing

namespace StrongThinTree.Packing
noncomputable section
variable {E : Type uE4} {V : Type uV2} {W : Type uW} [Fintype E] [DecidableEq E]
  [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]

omit [Fintype E] [DecidableEq E] [FiniteDimensional ℝ V] in
lemma span_smul (v : E → V) (s : E → ℝ) (hs : ∀ e, s e ≠ 0) (U : Finset E) :
    span (fun e => s e • v e) U = span v U := by
  apply le_antisymm
  · apply (span_le_iff _).mpr
    intro e he
    exact Submodule.smul_mem _ _ (mem_span_self v he)
  · apply (span_le_iff _).mpr
    intro e he
    have h := Submodule.smul_mem (span (fun e => s e • v e) U) (s e)⁻¹
      (mem_span_self (fun e => s e • v e) he)
    simpa only [smul_smul, inv_mul_cancel₀ (hs e), one_smul] using h

omit [Fintype E] [DecidableEq E] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
lemma span_map (v : E → V) (L : V →ₗ[ℝ] W) (U : Finset E) :
    span (fun e => L (v e)) U = (span v U).map L := by
  rw [span, Submodule.map_span, ← Set.image_image]

omit [Fintype E] [DecidableEq E] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
lemma rank_injective_map (v : E → V) (L : V →ₗ[ℝ] W)
    (hL : Function.Injective L) (U : Finset E) :
    Module.finrank ℝ (span (fun e => L (v e)) U) = Module.finrank ℝ (span v U) := by
  rw [span_map]
  exact (Submodule.equivMapOfInjective L hL (span v U)).finrank_eq.symm

end
end StrongThinTree.Packing

namespace StrongThinTree.MultiGraph
noncomputable section
open Matrix StrongThinTree.Packing
variable {n m : ℕ} (G : StrongThinTree.MultiGraph n m)

lemma represented_rank (L : zeroSumSpace n ≃ₗ[ℝ] (Fin (n-1) → ℝ))
    (s : Fin m → ℝ) (hs : ∀ e, s e ≠ 0) (U : Finset (Fin m)) :
    Module.finrank ℝ (Packing.span
      (fun e => s e • L ⟨G.incidence e, G.incidence_zeroSum e⟩) U) =
      Module.finrank ℝ (G.edgeSpan U) := by
  rw [Packing.span_smul _ s hs]
  change Module.finrank ℝ (Packing.span
    (fun e => L.toLinearMap (⟨G.incidence e, G.incidence_zeroSum e⟩ : zeroSumSpace n)) U) = _
  rw [Packing.rank_injective_map _ L.toLinearMap L.injective]
  symm
  exact Packing.rank_injective_map
    (fun e => (⟨G.incidence e, G.incidence_zeroSum e⟩ : zeroSumSpace n))
    (zeroSumSpace n).subtype Subtype.val_injective U

theorem represented_frame_treePackable (hn : 2 ≤ n)
    (L : zeroSumSpace n ≃ₗ[ℝ] (Fin (n-1) → ℝ))
    (s : Fin m → ℝ) (hs : ∀ e, 0 < s e) (A : Finset (Fin m))
    {r : ℕ} {c h : ℝ} (hc : 0 < c) (hh : 0 < h) (hr : (r : ℝ) * h ≤ c)
    (hnorm : ∀ e ∈ A, let z := s e • L ⟨G.incidence e, G.incidence_zeroSum e⟩
      z ⬝ᵥ z ≤ h)
    (hlow : ∀ x : Fin (n-1) → ℝ, c * (x ⬝ᵥ x) ≤
      ∑ e ∈ A, (x ⬝ᵥ (s e • L ⟨G.incidence e, G.incidence_zeroSum e⟩)) ^ 2) :
    G.TreePackable A r := by
  classical
  let z := fun e => s e • L ⟨G.incidence e, G.incidence_zeroSum e⟩
  let J := (WithLp.linearEquiv 2 ℝ (Fin (n-1) → ℝ)).symm
  let v := fun e => J (z e)
  have hnorm' : ∀ e ∈ A, ‖v e‖ ^ 2 ≤ h := by
    intro e he
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa [v, J, z, dotProduct, pow_two] using hnorm e he
  have hlow' : ∀ x : EuclideanSpace ℝ (Fin (n-1)),
      c * ‖x‖ ^ 2 ≤ ∑ e ∈ A, (inner ℝ x (v e)) ^ 2 := by
    intro x
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa [EuclideanSpace.inner_eq_star_dotProduct,
      v, J, z, dotProduct, pow_two, mul_comm] using hlow x.ofLp
  have hrank (U : Finset (Fin m)) :
      Module.finrank ℝ (Packing.span v U) = Module.finrank ℝ (G.edgeSpan U) := by
    change Module.finrank ℝ (Packing.span (fun e => J.toLinearMap (z e)) U) = _
    rw [Packing.rank_injective_map z J.toLinearMap J.injective]
    exact G.represented_rank L s (fun e => ne_of_gt (hs e)) U
  have htop := Packing.lower_frame_span v A hc hnorm' hlow'
  have hfull : Module.finrank ℝ (G.edgeSpan A) = n-1 := by
    rw [← hrank, htop, finrank_top]
    simp
  obtain ⟨F, hF, hFA⟩ := Packing.projected_trace_base_packing v A hc hh hr hnorm' hlow'
  refine ⟨F, ?_, hF.2⟩
  intro i
  refine ⟨(hFA i).1, (G.spanningTree_iff_independent (F i)).mpr ⟨?_, ?_⟩⟩
  · have hdim : Module.finrank ℝ (G.edgeSpan (F i)) = n-1 := by
      rw [← hrank, (hFA i).2, finrank_top]
      simp
    apply G.connected_of_componentCount_eq_one
    have hcomp := G.incidence_rank (F i)
    have hpos := G.componentCount_pos (by omega) (F i)
    omega
  · apply linearIndependent_iff_card_eq_finrank_span.mpr
    have heq : Set.range (fun e : (F i : Set (Fin m)) => G.incidence e) =
        G.incidence '' (F i : Set (Fin m)) := by ext x; simp
    change Fintype.card ↥(F i : Set (Fin m)) = Module.finrank ℝ (Submodule.span ℝ _)
    rw [heq]
    simpa [← hrank] using (Packing.indep_rank v (hF.1 i)).symm

end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Normalization_Descent
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalization descent. -/

section

namespace AlgorithmicThinTrees.Normalization
open Matrix Finset StrongThinTree
open scoped MatrixOrder

section Covariance
variable {E I : Type*} [normalizationFintypeE : Fintype E]
  [normalizationDecidableEqE : DecidableEq E] [normalizationFintypeI : Fintype I]
  [normalizationDecidableEqI : DecidableEq I]

omit normalizationFintypeI normalizationDecidableEqI in
lemma covariance_shrink [_covarianceShrinkFintypeI : Fintype I]
    [_covarianceShrinkDecidableEqI : DecidableEq I] {K : Type*} [Field K] (v : E → I → K)
    (a : E → K) (e : E) (δ : K) :
    covariance v (shrink δ a e) = covariance v a - (δ*a e) • vecMulVec (v e) (v e) := by
  classical
  have h : (fun f => shrink δ a e f • vecMulVec (v f) (v f)) =
      Function.update (fun f => a f • vecMulVec (v f) (v f)) e
        (((1-δ)*a e) • vecMulVec (v e) (v e)) := by
    funext f
    by_cases he : f=e
    · subst f; simp [shrink]
    · simp only [shrink,Function.update_of_ne he]
  unfold covariance
  rw [h,Finset.sum_update_of_mem (mem_univ e),sdiff_singleton_eq_erase]
  rw [←Finset.add_sum_erase univ (fun f => a f • vecMulVec (v f) (v f)) (mem_univ e)]
  module

lemma log_shrink_sum {δ : ℝ} (hδ : δ < 1) {a : E → ℝ} (ha : ∀e, 0 < a e) (e : E) :
    (∑f, Real.log (shrink δ a e f)) = (∑f, Real.log (a f))+Real.log (1-δ) := by
  have h : (fun f => Real.log (shrink δ a e f)) =
      Function.update (fun f => Real.log (a f)) e (Real.log ((1-δ)*a e)) := by
    funext f
    by_cases he : f=e
    · subst f; simp [shrink]
    · simp only [shrink,Function.update_of_ne he]
  rw [h,Finset.sum_update_of_mem (mem_univ e),sdiff_singleton_eq_erase,
    Real.log_mul (sub_pos.mpr hδ).ne' (ha e).ne']
  rw [←Finset.add_sum_erase univ (fun f => Real.log (a f)) (mem_univ e)]
  ring

lemma det_rank_one (A : Matrix I I ℝ) (hA : A.PosDef) (v : I → ℝ) (c : ℝ) :
    (A+c • vecMulVec v v).det=A.det*(1+c*(v ⬝ᵥ (A⁻¹ *ᵥ v))) := by
  have he : (Matrix.replicateCol Unit (c • v) * Matrix.replicateRow Unit v)=c • vecMulVec v v := by
    ext i j
    simp [Matrix.mul_apply,smul_eq_mul,Matrix.vecMulVec_apply]
    ring
  rw [←he,Matrix.det_add_replicateCol_mul_replicateRow
    ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit),Matrix.det_unique (n := Unit)]
  congr 1
  simp only [Matrix.add_apply,Matrix.one_apply_eq]
  change 1+(v ᵥ* A⁻¹) ⬝ᵥ (c • v) = 1+c*(v ⬝ᵥ (A⁻¹ *ᵥ v))
  rw [dotProduct_smul,←Matrix.dotProduct_mulVec,smul_eq_mul]

lemma det_shrink (v : E → I → ℝ) (a : E → ℝ) (e : E) (δ : ℝ)
    (hA : (covariance v a).PosDef) :
    (covariance v (shrink δ a e)).det=(covariance v a).det*(1-δ*leverage v a e) := by
  rw [covariance_shrink,sub_eq_add_neg,←neg_smul,
    det_rank_one _ hA (v e) (-(δ*a e)),leverage]
  ring

omit normalizationDecidableEqE in
lemma leverage_test [_leverageTestDecidableEqE : DecidableEq E]
    (v : E → I → ℝ) (a : E → ℝ) (e : E)
    (hA : (covariance v a).PosDef) (ha : 0 < a e) {t : ℝ} (ht : 0 < t) :
    leverage v a e ≤ t ↔ (t • covariance v a - a e • vecMulVec (v e) (v e)).PosSemidef := by
  have h := resistance_order hA (Real.sqrt (a e) • v e) ht
  have hs : Real.sqrt (a e)*Real.sqrt (a e)=a e := Real.mul_self_sqrt ha.le
  simpa only [leverage,Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul,
    ←mul_assoc,hs,Matrix.smul_vecMulVec,Matrix.vecMulVec_smul,smul_smul] using h

lemma neg_log_one_sub {δ : ℝ} (_hδ : 0 ≤ δ) (hδ1 : δ ≤ 1/2) :
    -Real.log (1-δ) ≤ δ+2*δ^2 := by
  have hp : 0 < 1-δ := by linarith only [hδ1]
  have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
  rw [Real.log_inv] at hh
  have hfrac : (1-δ)⁻¹-1 ≤ δ+2*δ^2 := by
    rw [inv_eq_one_div,div_sub_one hp.ne',div_le_iff₀ hp]
    nlinarith [sq_nonneg δ,mul_nonneg (sq_nonneg δ) (show 0 ≤ 1-2*δ by linarith)]
  exact hh.trans hfrac

lemma objective_drop (q : ℕ) (hq : 1 ≤ q) (v : E → I → ℝ)
    (a : E → ℝ) (ha : ∀e, 0 < a e) (e : E) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/2)
    (hA : (covariance v a).PosDef) (hA' : (covariance v (shrink δ a e)).PosDef)
    (he : 1/(q:ℝ)+4*δ < leverage v a e) :
    objective q v (shrink δ a e) ≤ objective q v a-δ^2 := by
  have hδlt : δ < 1 := by linarith only [hδ1]
  have hd := det_shrink v a e δ hA
  have hp : 0 < 1-δ*leverage v a e := by
    have hh := hA'.det_pos
    rw [hd] at hh
    exact (mul_pos_iff_of_pos_left hA.det_pos).mp hh
  have hlog := Real.log_le_sub_one_of_pos hp
  have hneg := neg_log_one_sub hδ.le hδ1
  have hqR : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0:ℝ) < q := by linarith only [hqR]
  have hqinv : 1/(q:ℝ) ≤ 1 := (div_le_one hq0).mpr hqR
  have hobj : objective q v (shrink δ a e) = objective q v a+
      Real.log (1-δ*leverage v a e)-Real.log (1-δ)/q := by
    unfold objective
    rw [hd,Real.log_mul hA.det_pos.ne' hp.ne',log_shrink_sum hδlt ha e]
    ring
  rw [hobj]
  have hmain := mul_lt_mul_of_pos_left he hδ
  have hdiv := div_le_div_of_nonneg_right hneg hq0.le
  have hrem : (δ+2*δ^2)/(q:ℝ) ≤ δ/q+2*δ^2 := by
    rw [add_div]
    apply add_le_add_right
    exact (div_le_self (by positivity) hqR)
  have hcancel : δ*(1/(q:ℝ))=δ/q := by ring
  rw [neg_div] at hdiv
  rw [mul_add,hcancel] at hmain
  nlinarith only [hmain,hlog,hdiv,hrem,sq_nonneg δ]

lemma logdet_le_trace {A : Matrix I I ℝ} (hA : A.PosDef) : Real.log A.det ≤ A.trace := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues,hA.isHermitian.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  rw [Real.log_prod (fun i _ => (hA.eigenvalues_pos i).ne')]
  apply sum_le_sum
  intro i _
  exact (Real.log_le_sub_one_of_pos (hA.eigenvalues_pos i)).trans (by linarith)

end Covariance

section Bases
variable {E : Type*} [Fintype E] [basisPackingDecidableEqE : DecidableEq E] {q d : ℕ}

namespace BasisPacking
variable {v : E → Fin d → ℝ} (B : BasisPacking v q)

omit basisPackingDecidableEqE in
lemma covariance_eq [_covarianceEqDecidableEqE : DecidableEq E]
    (a : E → ℝ) (ha : ∀e, 0 < a e) :
    covariance v a=packingCov B.matrices (B.logWeights a) := by
  rw [packingCov_eq_sum,covariance,←B.edges.sum_comp]
  apply sum_congr rfl
  intro e _
  simp only [logWeights,PiLp.toLp_apply,Real.exp_log (ha _),matrices]

include B

lemma covariance_posDef (a : E → ℝ) (ha : ∀e, 0 < a e) : (covariance v a).PosDef := by
  have : Nonempty (Fin q) := Fin.pos_iff_nonempty.mp B.positive
  rw [B.covariance_eq a ha]
  exact packingCov_posDef B.matrices B.invertible _

lemma objective_nonneg (a : E → ℝ) (ha : ∀e, 0 < a e) : 0 ≤ objective q v a := by
  have : Nonempty (Fin q) := Fin.pos_iff_nonempty.mp B.positive
  have hn : ∀t, 0 ≤ Real.log ((B.matrices t).det^2) :=
    fun t => Real.log_nonneg (B.determinant t)
  have hb := packingObjective_bddBelow B.matrices B.invertible (B.logWeights a)
  have h0 : 0 ≤ (∑t, Real.log ((B.matrices t).det^2))/(Fintype.card (Fin q):ℝ) :=
    div_nonneg (sum_nonneg (fun t _ => hn t)) (Nat.cast_nonneg _)
  apply (h0.trans hb).trans_eq
  unfold packingObjective objective
  rw [←B.covariance_eq a ha,Fintype.card_fin]
  congr 2
  exact B.edges.sum_comp (fun e => Real.log (a e))

end BasisPacking
end Bases
end AlgorithmicThinTrees.Normalization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Normalization_Packing
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalization packing. -/

section

namespace AlgorithmicThinTrees.Normalization
open Matrix Finset StrongThinTree
open scoped MatrixOrder

lemma covariance_embedding {E J I : Type*} [Fintype E] [DecidableEq E]
    [Fintype J] [DecidableEq J] [Fintype I]
    (f : J ↪ E) (v : E → I → ℝ) (a : E → ℝ) :
    covariance v a=covariance (v ∘ f) (a ∘ f)+
      ∑e ∈ univ \ univ.map f, a e • vecMulVec (v e) (v e) := by
  unfold covariance
  simp only [Function.comp_apply]
  rw [←Finset.sum_map (f := fun e => a e • vecMulVec (v e) (v e))]
  exact (Finset.sum_sdiff (f := fun e => a e • vecMulVec (v e) (v e)) (subset_univ (univ.map f))).symm.trans (add_comm ..)

namespace ContainedPacking
variable {E : Type*} [Fintype E] [DecidableEq E] {q d : ℕ}
variable {v : E → Fin d → ℝ} (B : ContainedPacking v q)

include B
lemma extra_posSemidef (a : E → ℝ) (ha : ∀e, 0 ≤ a e) :
    (∑e ∈ univ \ univ.map B.edges, a e • vecMulVec (v e) (v e)).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro e _
  have h : (vecMulVec (v e) (v e)).PosSemidef := by
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (v e)
  exact h.smul (ha e)

lemma covariance_posDef (a : E → ℝ) (ha : ∀e, 0 < a e) : (covariance v a).PosDef := by
  rw [covariance_embedding B.edges v a]
  exact (B.full.covariance_posDef (a ∘ B.edges) (fun e => ha _)).add_posSemidef
    (B.extra_posSemidef a (fun e => (ha e).le))

lemma objective_nonneg (a : E → ℝ) (ha : ∀e, 0 < a e) (ha1 : ∀e, a e ≤ 1) :
    0 ≤ objective q v a := by
  have hb := B.full.objective_nonneg (a ∘ B.edges) (fun e => ha _)
  have hpd := B.full.covariance_posDef (a ∘ B.edges) (fun e => ha _)
  have hd : (covariance (v ∘ B.edges) (a ∘ B.edges)).det ≤ (covariance v a).det := by
    rw [covariance_embedding B.edges v a]
    exact det_le_det_add_of_posSemidef hpd (B.extra_posSemidef a (fun e => (ha e).le))
  have hl := Real.log_le_log hpd.det_pos hd
  have hlogs : (∑e, Real.log (a e)) ≤ ∑j, Real.log (a (B.edges j)) := by
    rw [←Finset.sum_map (f := fun e => Real.log (a e))]
    have hsum := Finset.sum_sdiff (f := fun e => Real.log (a e)) (subset_univ (univ.map B.edges))
    have hnonpos : ∑e ∈ univ \ univ.map B.edges, Real.log (a e) ≤ 0 :=
      sum_nonpos (fun e _ => Real.log_nonpos (ha e).le (ha1 e))
    linarith only [hsum,hnonpos]
  have hdiv := div_le_div_of_nonneg_right hlogs (Nat.cast_nonneg q : (0:ℝ)≤q)
  unfold objective at hb ⊢
  exact hb.trans (sub_le_sub hl hdiv)

lemma initial_gap (hsize : ∀e, v e ⬝ᵥ v e ≤ 2) :
    objective q v (fun _ => 1) ≤ 2*Fintype.card E := by
  have hh := logdet_le_trace (B.covariance_posDef (fun _ => 1) (by simp))
  simp only [objective,Real.log_one,sum_const_zero,zero_div,sub_zero]
  apply hh.trans
  simp only [covariance,one_smul,Matrix.trace_sum,Matrix.trace_vecMulVec]
  calc
    _ ≤ ∑_e : E, (2:ℝ) := sum_le_sum (fun e _ => hsize e)
    _ = _ := by simp [mul_comm]

end ContainedPacking
end AlgorithmicThinTrees.Normalization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Normalization_Algorithm
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalization algorithm. -/

section

namespace AlgorithmicThinTrees.Normalization
open Matrix Finset StrongThinTree
open scoped MatrixOrder
variable {m d : ℕ}

lemma scalesAt_zero (q : ℕ) (t : ℚ) (v : Fin m → Fin d → ℚ) :
    scalesAt q t v 0=(fun _ => 1) := rfl

lemma realWeights_one : realWeights (fun _ : Fin m => 1)=(fun _ => (1:ℝ)) := by
  funext e
  simp only [realWeights,Rat.cast_one,one_pow]

lemma testMatrix_symm (q : ℕ) (t : ℚ) (v : Fin m → Fin d → ℚ)
    (s : Fin m → ℚ) (e : Fin m) : (testMatrix q t v s e).IsSymm := by
  change (testMatrix q t v s e)ᵀ=testMatrix q t v s e
  simp only [testMatrix,covariance,Matrix.transpose_sub,Matrix.transpose_smul,
    Matrix.transpose_sum,Matrix.transpose_vecMulVec]

lemma testMatrix_cast (q : ℕ) (t : ℚ) (v : Fin m → Fin d → ℚ)
    (s : Fin m → ℚ) (e : Fin m) :
    (testMatrix q t v s e).map (fun x : ℚ => (x:ℝ)) =
      (threshold q t:ℝ) • covariance (realColumns v) (realWeights s)-
        (s e:ℝ)^2 • vecMulVec (realColumns v e) (realColumns v e) := by
  ext i j
  simp only [testMatrix,covariance,weights,realWeights,realColumns,
    Matrix.map_apply,Matrix.sub_apply,Matrix.smul_apply,Matrix.sum_apply,
    Matrix.vecMulVec_apply,smul_eq_mul,Rat.cast_sub,Rat.cast_mul,Rat.cast_pow,Rat.cast_sum]

lemma heavy_none (q : ℕ) (t : ℚ) (v : Fin m → Fin d → ℚ)
    (s : Fin m → ℚ) (hs : ∀e, 0 < s e)
    (hA : (covariance (realColumns v) (realWeights s)).PosDef)
    (ht : 0 < threshold q t) :
    heavy q t v s=none ↔ ∀e, leverage (realColumns v) (realWeights s) e ≤ (threshold q t:ℝ) := by
  rw [heavy,List.find?_eq_none]
  simp only [List.mem_finRange,forall_const,Option.isSome_iff_ne_none,not_not]
  apply forall_congr'
  intro e
  rw [KS.W17.rationalNegativeWitness_none_iff_psd _ _ (testMatrix_symm ..),testMatrix_cast]
  exact (leverage_test (realColumns v) (realWeights s) e hA
    (sq_pos_of_pos (by exact_mod_cast hs e)) (by exact_mod_cast ht)).symm

lemma heavy_some (q : ℕ) (t : ℚ) (v : Fin m → Fin d → ℚ)
    (s : Fin m → ℚ) (hs : ∀e, 0 < s e)
    (hA : (covariance (realColumns v) (realWeights s)).PosDef)
    (ht : 0 < threshold q t) {e : Fin m} (he : heavy q t v s=some e) :
    (threshold q t:ℝ) < leverage (realColumns v) (realWeights s) e := by
  have hh := List.find?_some he
  rw [Option.isSome_iff_ne_none] at hh
  simp only [ne_eq, KS.W17.rationalNegativeWitness_none_iff_psd _ _ (testMatrix_symm ..),testMatrix_cast] at hh
  exact lt_of_not_ge (fun hc => hh ((leverage_test (realColumns v) (realWeights s) e hA
    (sq_pos_of_pos (by exact_mod_cast hs e)) (by exact_mod_cast ht)).mp hc))

lemma update_realWeights (s : Fin m → ℚ) (t : ℚ) (e : Fin m) :
    realWeights (Function.update s e (t*s e))=shrink (decrement t:ℝ) (realWeights s) e := by
  funext f
  by_cases h : f=e
  · subst f
    simp only [realWeights,shrink,Function.update_self,decrement,Rat.cast_sub,Rat.cast_one,Rat.cast_pow,Rat.cast_mul]
    ring
  · simp only [realWeights,shrink,Function.update_of_ne h]

lemma advance_box (q : ℕ) {t : ℚ} (ht : 0 < t) (ht1 : t ≤ 1)
    (v : Fin m → Fin d → ℚ) (s : Fin m → ℚ)
    (hs : ∀e, 0 < s e ∧ s e ≤ 1) : ∀e, 0 < advance q t v s e ∧ advance q t v s e ≤ 1 := by
  unfold advance
  cases he : heavy q t v s with
  | none => simpa only [Option.elim_none] using hs
  | some f =>
    intro e
    simp only [Option.elim_some]
    by_cases h : e=f
    · subst e
      simp only [Function.update_self]
      exact ⟨mul_pos ht (hs f).1,(mul_le_of_le_one_left (hs f).1.le ht1).trans (hs f).2⟩
    · simpa only [Function.update_of_ne h] using hs e

lemma scalesAt_box (q : ℕ) {t : ℚ} (ht : 0 < t) (ht1 : t ≤ 1)
    (v : Fin m → Fin d → ℚ) (k : ℕ) : ∀e, 0 < scalesAt q t v k e ∧ scalesAt q t v k e ≤ 1 := by
  induction k with
  | zero => simp [scalesAt]
  | succ k ih =>
    change ∀e, 0 < ((advance q t v)^[k+1] (fun _ => 1)) e ∧
      ((advance q t v)^[k+1] (fun _ => 1)) e ≤ 1
    rw [Function.iterate_succ_apply']
    exact advance_box q ht ht1 v _ ih

lemma realWeights_box {s : Fin m → ℚ} (hs : ∀e, 0 < s e ∧ s e ≤ 1) :
    (∀e, 0 < realWeights s e) ∧ (∀e, realWeights s e ≤ 1) := by
  have hr (e : Fin m) : (0:ℝ) < s e ∧ (s e:ℝ) ≤ 1 := by exact_mod_cast hs e
  constructor
  · intro e;exact sq_pos_of_pos (hr e).1
  · intro e;exact pow_le_one₀ (hr e).1.le (hr e).2

lemma scalesAt_terminates (q : ℕ) {t : ℚ} (ht : 0 < t) (ht1 : t < 1)
    (hδ : 0 < decrement t) (hδ1 : decrement t ≤ 1/2)
    (v : Fin m → Fin d → ℚ) (B : ContainedPacking (realColumns v) q)
    (hsize : ∀e, realColumns v e ⬝ᵥ realColumns v e ≤ 2) (N : ℕ)
    (hN : 2*(m:ℝ) < N*(decrement t:ℝ)^2) :
    heavy q t v (scalesAt q t v N)=none := by
  have hq : 1 ≤ q := B.positive
  have hth : 0 < threshold q t := by
    unfold threshold
    have hq0 : (0:ℚ)<q := by exact_mod_cast B.positive
    positivity
  have hbox (k : ℕ) := realWeights_box (scalesAt_box q ht ht1.le v k)
  have hbound (k : ℕ) : heavy q t v (scalesAt q t v k)=none ∨
      objective q (realColumns v) (realWeights (scalesAt q t v k)) ≤
        2*m-k*(decrement t:ℝ)^2 := by
    induction k with
    | zero =>
      right
      rw [scalesAt_zero,realWeights_one]
      simpa only [Nat.cast_zero,zero_mul,sub_zero,Fintype.card_fin] using B.initial_gap hsize
    | succ k ih =>
      have heq : scalesAt q t v (k+1)=advance q t v (scalesAt q t v k) :=
        Function.iterate_succ_apply' _ _ _
      cases hh : heavy q t v (scalesAt q t v k) with
      | none =>
        left
        rw [heq,advance,hh,Option.elim_none,hh]
      | some e =>
        right
        have hi := ih.resolve_left (by rw [hh];simp)
        have hp := B.covariance_posDef _ (hbox k).1
        have hheavy := heavy_some q t v _ (fun e => (scalesAt_box q ht ht1.le v k e).1) hp hth hh
        have hstep : scalesAt q t v (k+1)=Function.update (scalesAt q t v k) e
            (t*scalesAt q t v k e) := by rw [heq,advance,hh,Option.elim_some]
        have hweights : realWeights (scalesAt q t v (k+1)) =
            shrink (decrement t:ℝ) (realWeights (scalesAt q t v k)) e := by
          rw [hstep,update_realWeights]
        have hp' := B.covariance_posDef _ (hbox (k+1)).1
        rw [hweights] at hp'
        have hd := objective_drop q hq (realColumns v) _ (hbox k).1 e (decrement t:ℝ)
          (by exact_mod_cast hδ) (by
            have hh : (decrement t:ℝ) ≤ (((1:ℚ)/2:ℚ):ℝ) := Rat.cast_le.mpr hδ1
            norm_num at hh ⊢
            exact hh) hp hp' (by
            simpa only [threshold,Rat.cast_add,Rat.cast_div,Rat.cast_one,Rat.cast_natCast,
              Rat.cast_mul,Rat.cast_ofNat] using hheavy)
        rw [hweights]
        push_cast
        nlinarith only [hi,hd]
  rcases hbound N with h|h
  · exact h
  · have h0 := B.objective_nonneg _ (hbox N).1 (hbox N).2
    linarith only [h,h0,hN]

lemma scalesAt_parts (q : ℕ) (t : ℚ) (v : Fin m → Fin d → ℚ)
    {b : ℕ} (ht : CurrentKS.RationalBits.Parts b t) (k : ℕ) :
    ∀e, CurrentKS.RationalBits.Parts (k*b) (scalesAt q t v k e) := by
  induction k with
  | zero => intro e;norm_num [scalesAt,CurrentKS.RationalBits.Parts]
  | succ k ih =>
    intro e
    change CurrentKS.RationalBits.Parts ((k+1)*b) (((advance q t v)^[k+1] (fun _ => 1)) e)
    rw [Function.iterate_succ_apply']
    change CurrentKS.RationalBits.Parts ((k+1)*b) (advance q t v (scalesAt q t v k) e)
    unfold advance
    cases hh : heavy q t v (scalesAt q t v k) with
    | none => exact (ih e).mono (Nat.mul_le_mul_right b (Nat.le_succ k))
    | some f =>
      simp only [Option.elim_some]
      by_cases h : e=f
      · subst e
        simpa only [Function.update_self,Nat.add_mul,Nat.one_mul,Nat.add_comm] using ht.mul (ih f)
      · simpa only [Function.update_of_ne h] using (ih e).mono (Nat.mul_le_mul_right b (Nat.le_succ k))

end AlgorithmicThinTrees.Normalization
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

lemma eval_difference (x : Fin n → ℝ) (u v : Fin n) :
    x ⬝ᵥ difference u v=x u-x v := by
  simp [difference,point,dotProduct_sub]

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

lemma centeredTest_mul_constant {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : CenteredTest Z) :
    Z*constantProjection n=0 := by
  have h0 : Z *ᵥ ones n=0 := hZ.2
  simp only [constantProjection,mul_smul_comm,mul_vecMulVec,h0,zero_vecMulVec,smul_zero]

lemma centeredTest_constant_mul {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : CenteredTest Z) :
    constantProjection n*Z=0 := by
  have hh := congrArg transpose (centeredTest_mul_constant hZ)
  simpa only [transpose_mul,constantProjection_symmetric,
    (isHermitian_iff_isSymm.mp hZ.1.1.isHermitian).eq,transpose_zero] using hh

lemma regularize_trace (D : Matrix (Fin n) (Fin n) ℝ)
    {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : CenteredTest Z) :
    (regularize D*Z).trace=(D*Z).trace := by
  rw [regularize,add_mul,trace_add,centeredTest_constant_mul hZ,trace_zero,add_zero]

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

lemma trace_pairing_mono {B D Z : Matrix (Fin n) (Fin n) ℝ}
    (hBD : B ≤ D) (hZ : Z.PosSemidef) : (B*Z).trace ≤ (D*Z).trace := by
  have hh := trace_pairing_nonneg (Matrix.le_iff.mp hBD) hZ
  simpa only [sub_mul,trace_sub,sub_nonneg] using hh

end Pairing
end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_CenteredDomain
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
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

lemma difference_sum (u v : Fin n) : (∑i, difference u v i)=0 := by
  simp [difference,point,sum_sub_distrib]

lemma test_centered (hn : 0 < n) {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Test Z) :
    CenteredTest (centered Z) := by
  refine ⟨⟨centered_psd hZ.1,?_⟩,centered_ones hn Z⟩
  intro u v w
  simpa only [qform_centered,centering_mulVec_of_sum_zero (difference_sum _ _)] using hZ.2 u v w

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_StepBounds
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter
open scoped Topology
namespace StrongThinTree

end StrongThinTree

end
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Schedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation schedule. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped MatrixOrder
variable {n m : ℕ}

lemma nthRoot_le_real_root (d r : ℕ) (hd : 0 < d) :
    (Nat.nthRoot d r:ℝ) ≤ (r:ℝ)^(1/(d:ℝ)) := by
  rw [one_div,Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_pos.mpr hd),Real.rpow_natCast]
  exact_mod_cast Nat.pow_nthRoot_le (n:=d) (a:=r) (.inl hd.ne')

lemma real_root_lt_nthRoot_add (d r : ℕ) (hd : 0 < d) :
    (r:ℝ)^(1/(d:ℝ)) < (Nat.nthRoot d r:ℝ)+1 := by
  rw [one_div,Real.rpow_inv_lt_iff_of_pos (Nat.cast_nonneg _) (by positivity)
    (Nat.cast_pos.mpr hd),Real.rpow_natCast]
  exact_mod_cast Nat.lt_pow_nthRoot_add_one hd.ne' r

lemma nthRoot_pos (d r : ℕ) (hd : 0 < d) (hr : 0 < r) :
    1 ≤ Nat.nthRoot d r := by
  rw [Nat.le_nthRoot_iff hd.ne',one_pow]
  exact hr

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Start
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation start. -/

section

namespace AlgorithmicThinTrees.MetricTests
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped MatrixOrder
variable {n m : ℕ}

lemma packing_connected (H : MultiGraph n m) {r : ℕ} (hr : 0 < r)
    (hp : H.TreePackable univ r) : H.Connected univ := by
  intro S hS hS'
  apply card_pos.mp
  exact hr.trans_le (H.treePackable_edgeConnected hp S hS hS')

end AlgorithmicThinTrees.MetricTests

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_IterationBounds
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace StrongThinTree

lemma errorU_nonneg (r : ℕ) : 0 ≤ errorU r := Real.rpow_nonneg (Nat.cast_nonneg _) _
end StrongThinTree

end
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Normalization_Parameters
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalization parameters. -/

section

namespace AlgorithmicThinTrees.Normalization
open Matrix Finset StrongThinTree
open scoped MatrixOrder

lemma multiplier_bounds (r : ℕ) (hr : 1 ≤ r) :
    0 < multiplier r ∧ multiplier r < 1 ∧
    0 < decrement (multiplier r) ∧ decrement (multiplier r) ≤ 1/2 ∧
    1/(16*(r:ℚ)^2) ≤ decrement (multiplier r) ∧
    decrement (multiplier r) ≤ 1/(8*(r:ℚ)^2) := by
  have hr1 : (1:ℚ) ≤ r := by exact_mod_cast hr
  have hr2 : (1:ℚ) ≤ (r:ℚ)^2 := one_le_pow₀ hr1
  have hd : (0:ℚ) < 16*(r:ℚ)^2 := by positivity
  have hx : (0:ℚ) < 1/(16*(r:ℚ)^2) := div_pos zero_lt_one hd
  have hx1 : (1:ℚ)/(16*(r:ℚ)^2) ≤ 1/16 := by
    rw [div_le_div_iff₀ hd (by norm_num : (0:ℚ)<16)]
    linarith only [hr2]
  have he : 1/(8*(r:ℚ)^2)=2*(1/(16*(r:ℚ)^2)) := by ring
  unfold multiplier decrement
  rw [he]
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> nlinarith [sq_nonneg (1/(16*(r:ℚ)^2))]

lemma normalizationLength_suffices (m r : ℕ) (hr : 1 ≤ r) :
    2*(m:ℝ) < (normalizationLength m r:ℝ)*(decrement (multiplier r):ℝ)^2 := by
  have hr0 : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hδ := (multiplier_bounds r hr).2.2.2.2.1
  have hδR : 1/(16*(r:ℝ)^2) ≤ (decrement (multiplier r):ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hδ
    simpa only [Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_pow,
      Rat.cast_natCast,Rat.cast_one] using hh
  have hsq := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 1/(16*(r:ℝ)^2)) hδR 2
  have hN : (normalizationLength m r:ℝ)=(2*(m:ℝ)+1)*256*(r:ℝ)^4 := by
    simp only [normalizationLength,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one,Nat.cast_pow]
  have he : (normalizationLength m r:ℝ)*(1/(16*(r:ℝ)^2))^2=2*(m:ℝ)+1 := by
    rw [hN]
    field_simp [ne_of_gt hr0]
    ring
  have hh := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg (normalizationLength m r) : (0:ℝ) ≤ _)
  rw [he] at hh
  linarith only [hh]

lemma threshold_le (q r : ℕ) (hq : 0 < q) (hqr : q ≤ r) :
    (threshold q (multiplier r):ℝ) ≤ (1+4/(r:ℝ))/(q:ℝ) := by
  have hr : 1 ≤ r := Nat.le_trans hq hqr
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hrR : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hqrR : (q:ℝ) ≤ r := by exact_mod_cast hqr
  have hδ := (multiplier_bounds r hr).2.2.2.2.2
  have hδR : (decrement (multiplier r):ℝ) ≤ 1/(8*(r:ℝ)^2) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hδ
    simpa only [Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_pow,
      Rat.cast_natCast,Rat.cast_one] using hh
  have hh : 4*(decrement (multiplier r):ℝ) ≤ 4/((r:ℝ)*q) := by
    apply (mul_le_mul_of_nonneg_left hδR (by norm_num : (0:ℝ) ≤ 4)).trans
    have hc : (r:ℝ)*q ≤ 8*(r:ℝ)^2 := by nlinarith only [mul_le_mul_of_nonneg_left hqrR hrR.le,sq_nonneg (r:ℝ)]
    have hi := one_div_le_one_div_of_le (mul_pos hrR hqR) hc
    calc
      4*(1/(8*(r:ℝ)^2)) ≤ 4*(1/((r:ℝ)*q)) := mul_le_mul_of_nonneg_left hi (by norm_num)
      _ = _ := by ring
  simp only [threshold,Rat.cast_add,Rat.cast_div,Rat.cast_one,Rat.cast_natCast,
    Rat.cast_mul,Rat.cast_ofNat]
  have he : (1+4/(r:ℝ))/(q:ℝ)=1/(q:ℝ)+4/((r:ℝ)*q) := by ring
  rw [he]
  linarith only [hh]

lemma multiplier_parts (r : ℕ) :
    CurrentKS.RationalBits.Parts (5+2*r.size) (multiplier r) := by
  have hr := CurrentKS.RationalBits.natCast_parts r
  have h16 : CurrentKS.RationalBits.Parts 4 (16:ℚ) := by norm_num [CurrentKS.RationalBits.Parts]
  have hh := CurrentKS.RationalBits.parts_one.add ((h16.mul (hr.mul hr)).inv.neg)
  convert hh using 1
  · omega
  · simp only [multiplier,sub_eq_add_neg,one_div,pow_two]

theorem normalizedScales_correct {m d q r : ℕ} (v : Fin m → Fin d → ℚ)
    (B : ContainedPacking (realColumns v) q) (hqr : q ≤ r)
    (hsize : ∀e, realColumns v e ⬝ᵥ realColumns v e ≤ 2) :
    let s := normalizedScales q r v
    (∀e, 0 < s e ∧ s e ≤ 1) ∧
    (∀e, leverage (realColumns v) (realWeights s) e ≤ (1+4/(r:ℝ))/(q:ℝ)) ∧
    (∀e, CurrentKS.RationalBits.Parts (normalizationLength m r*(5+2*r.size)) (s e)) := by
  have hr : 1 ≤ r := B.positive.trans_le hqr
  obtain ⟨ht,ht1,hδ,hδ1,hδlower,hδupper⟩ := multiplier_bounds r hr
  have hbox := scalesAt_box q ht ht1.le v (normalizationLength m r)
  have hA := B.covariance_posDef _ (realWeights_box hbox).1
  have hq0 : (0:ℚ) < q := by exact_mod_cast B.positive
  have hth : 0 < threshold q (multiplier r) := by unfold threshold; positivity
  have hN := scalesAt_terminates q ht ht1 hδ hδ1 v B hsize
    (normalizationLength m r) (normalizationLength_suffices m r hr)
  refine ⟨hbox,?_,scalesAt_parts q _ v (multiplier_parts r) _⟩
  intro e
  exact (((heavy_none q (multiplier r) v _ (fun e => (hbox e).1) hA hth).mp hN) e).trans
    (threshold_le q r B.positive hqr)

end AlgorithmicThinTrees.Normalization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Signing_GramWhitening
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gram whitening. -/

section

namespace AlgorithmicThinTrees.GramWhitening
open Matrix Finset
open scoped MatrixOrder
variable {n d m : ℕ}

lemma congruence_mono {A B : Matrix (Fin n) (Fin n) ℝ} (h : A ≤ B)
    (R : Matrix (Fin n) (Fin d) ℝ) : Rᵀ*A*R ≤ Rᵀ*B*R := by
  rw [Matrix.le_iff]
  have hh := (Matrix.le_iff.mp h).conjTranspose_mul_mul_same R
  simpa only [conjTranspose_eq_transpose_of_trivial,Matrix.mul_sub,Matrix.sub_mul] using hh

lemma rectangular_norm (R : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ) :
    (Rᵀ*ᵥb) ⬝ᵥ (Rᵀ*ᵥb)=b ⬝ᵥ ((R*Rᵀ)*ᵥb) := by
  rw [dotProduct_mulVec,vecMul_transpose,dotProduct_comm,←mulVec_mulVec,dotProduct_mulVec]

lemma congruence_outer (R : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ) :
    vecMulVec (Rᵀ*ᵥb) (Rᵀ*ᵥb) = Rᵀ*vecMulVec b b*R := by
  rw [mul_vecMulVec,vecMulVec_mul,←vecMul_transpose Rᵀ,transpose_transpose]

lemma congruence_sum_outer (R : Matrix (Fin n) (Fin d) ℝ)
    (b : Fin m → Fin n → ℝ) (A : Finset (Fin m)) :
    (∑e∈A,vecMulVec (Rᵀ*ᵥb e) (Rᵀ*ᵥb e)) = Rᵀ*(∑e∈A,vecMulVec (b e) (b e))*R := by
  simp only [congruence_outer,Matrix.mul_sum,Matrix.sum_mul]

end AlgorithmicThinTrees.GramWhitening
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Sparsification_GraphicNormalization
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Graphic normalization. -/

section

namespace AlgorithmicThinTrees.Normalization
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
variable {d m q : ℕ}

lemma graphColumns_cast (G : MultiGraph (d+1) m) (B : Finset (Fin m)) (e : Fin m) :
    realColumns (graphColumns G B) e = if e ∈ B then
      dropRoot d ⟨G.incidence e,G.incidence_zeroSum e⟩ else 0 := by
  funext i
  by_cases he : e ∈ B
  · rw [ite_eq_left he]
    change ((integerColumns G B e i : ℚ):ℝ) = G.incidence e i.succ
    simp only [integerColumns,ite_eq_left he,Int.cast_sub,incidence,
      point,Pi.sub_apply,Pi.single_apply,eq_comm (a:=i.succ)]
    split_ifs <;> norm_num
  · simp [he,realColumns,graphColumns,integerColumns]

lemma graphColumns_norm (G : MultiGraph (d+1) m) (B : Finset (Fin m)) (e : Fin m) :
    realColumns (graphColumns G B) e ⬝ᵥ realColumns (graphColumns G B) e ≤ 2 := by
  rw [graphColumns_cast]
  split_ifs with he
  · have hh := G.eval_incidence (G.incidence e) e
    have hnorm : G.incidence e ⬝ᵥ G.incidence e=2 := by
      rw [dotProduct,hh]
      norm_num [incidence,point,G.loopless e,Ne.symm (G.loopless e)]
    rw [dotProduct,Fin.sum_univ_succ] at hnorm
    change (∑i : Fin d, G.incidence e i.succ*G.incidence e i.succ) ≤ 2
    nlinarith only [hnorm,sq_nonneg (G.incidence e 0)]
  · simp

lemma integral_det_bound (v : Fin d → Fin d → ℤ)
    (hv : IsUnit (Matrix.of (fun i j => (v i j:ℝ)))) :
    1 ≤ (Matrix.det (fun i j => (v i j:ℝ)))^2 := by
  have hdet : (Matrix.of v).det ≠ 0 := by
    intro hh
    have hR : (Matrix.of (fun i j => (v i j:ℝ))).det=0 := by
      have hc := (Int.cast_det (R := ℝ) (Matrix.of v)).symm
      rw [hh,Int.cast_zero] at hc
      exact hc
    exact (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hv)) hR
  have hpos : (0:ℤ) < (Matrix.of v).det^2 := sq_pos_of_ne_zero hdet
  have h1 : (1:ℤ) ≤ (Matrix.of v).det^2 := by omega
  have hR : (1:ℝ) ≤ ((Matrix.of v).det:ℝ)^2 := by exact_mod_cast h1
  rw [Int.cast_det] at hR
  exact hR

lemma integral_containedPacking {E : Type*} [DecidableEq E]
    (v : E → Fin d → ℤ) (F : Fin q → Finset E) (hq : 0 < q)
    (hF : ∀t, LinearIndepOn ℝ (fun e i => (v e i:ℝ)) (F t : Set E))
    (hc : ∀t, (F t).card=d) (hd : Pairwise (fun i j => Disjoint (F i) (F j))) :
    Nonempty (ContainedPacking (fun e i => (v e i:ℝ)) q) := by
  classical
  let en (t : Fin q) : Fin d ≃ ↥(F t) := Fintype.equivOfCardEq (by simp [hc])
  let f : Fin q × Fin d → E :=fun x => en x.1 x.2
  have hinj : Function.Injective f := by
    rintro ⟨t,i⟩ ⟨u,j⟩ hh
    have hev : (en t i:E)=(en u j:E) := hh
    have htu : t=u := by
      by_contra h
      exact Finset.disjoint_left.mp (hd h) (en t i).property (hev ▸ (en u j).property)
    subst u
    have hij := (en t).injective (Subtype.ext hev)
    subst j
    rfl
  have hb (t : Fin q) : IsUnit (Matrix.of (fun i j => (v (en t j) i:ℝ))) := by
    apply Matrix.mulVec_injective_iff_isUnit.mp
    apply Matrix.mulVec_injective_iff.mpr
    exact (hF t).linearIndependent.comp (en t) (en t).injective
  exact ⟨⟨hq,⟨f,hinj⟩,hb,fun t => integral_det_bound (fun i j => v (en t j) i) (hb t)⟩⟩

lemma graph_containedPacking (G : MultiGraph (d+1) m) (B : Finset (Fin m))
    (hq : 0 < q) (hp : G.TreePackable B q) :
    Nonempty (ContainedPacking (realColumns (graphColumns G B)) q) := by
  obtain ⟨F,hF,hd⟩ := hp
  have hv : realColumns (graphColumns G B) =
      fun e i => (integerColumns G B e i:ℝ) := by
    funext e i
    simp only [realColumns,graphColumns,Rat.cast_intCast]
  rw [hv]
  apply integral_containedPacking _ F hq ?_ ?_ hd
  · intro t
    have hf := ((G.spanningTree_iff_independent (F t)).mp (hF t).2).2.linearIndependent
    have hf' : LinearIndependent ℝ (fun e : ↥(F t) =>
        (⟨G.incidence e,G.incidence_zeroSum e⟩ : zeroSumSpace (d+1))) :=
      hf.of_comp (zeroSumSpace (d+1)).subtype
    have hl := hf'.map' (dropRoot d).toLinearMap (dropRoot d).ker
    change LinearIndependent ℝ (fun (e : ↥(F t)) (i : Fin d) => (integerColumns G B e i:ℝ))
    have hvec : (fun (e : ↥(F t)) (i : Fin d) => (integerColumns G B e i:ℝ)) =
        (dropRoot d).toLinearMap ∘ (fun e : ↥(F t) =>
          (⟨G.incidence e,G.incidence_zeroSum e⟩ : zeroSumSpace (d+1))) := by
      funext e i
      have he := graphColumns_cast G B e.val
      rw [hv,ite_eq_left ((hF t).1 e.property)] at he
      exact congrFun he i
    rw [hvec]
    exact hl
  · intro t
    simpa only [Nat.add_sub_cancel] using G.spanningTree_card (by omega : 0 < d+1) (hF t).2

theorem graphic_normalization (G : MultiGraph (d+1) m) (B : Finset (Fin m))
    {q r : ℕ} (hq : 0 < q) (hqr : q ≤ r) (hp : G.TreePackable B q) :
    let s := normalizedScales q r (graphColumns G B)
    (∀e, 0 < s e ∧ s e ≤ 1) ∧
    (∀e, leverage (realColumns (graphColumns G B)) (realWeights s) e ≤ (1+4/(r:ℝ))/(q:ℝ)) ∧
    (∀e, CurrentKS.RationalBits.Parts (normalizationLength m r*(5+2*r.size)) (s e)) := by
  obtain ⟨packing⟩ := graph_containedPacking G B hq hp
  exact normalizedScales_correct _ packing hqr (graphColumns_norm G B)

end AlgorithmicThinTrees.Normalization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Sparsification_GraphicHalf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Graphic half. -/

section

namespace AlgorithmicThinTrees.GraphicHalf
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open MetricTests MetricTests.RationalStep Normalization RationalSigning
open scoped MatrixOrder
variable {n d m : ℕ}

lemma fullColumns_cast (G : MultiGraph n m) (B : Finset (Fin m)) (e : Fin m) :
    realVec (fullColumns G B) e=if e ∈ B then G.incidence e else 0 := by
  ext i
  by_cases he : e ∈ B
  · simp only [realVec,fullColumns,ite_eq_left he,cast_qinc]
  · simp only [fullColumns,he,ite_false, if_false,realVec,Pi.zero_apply,Rat.cast_zero]

lemma positiveForm_cast (X : Matrix (Fin n) (Fin n) ℚ) :
    (positiveForm X).map (fun q : ℚ => (q:ℝ))=regularize (X.map (fun q : ℚ => (q:ℝ))) := by
  ext i j
  simp only [positiveForm,map_apply,Matrix.add_apply,Rat.cast_add,Matrix.of_apply,Rat.cast_inv,
    Rat.cast_natCast,regularize,constantProjection,Matrix.smul_apply,smul_eq_mul,vecMulVec,ones,mul_one]

lemma scaledColumns_cast (G : MultiGraph (d+1) m) (B : Finset (Fin m))
    (s : Fin m → ℚ) (e : Fin m) :
    realVec (scaledColumns G B s) e=(s e:ℝ) • realColumns (graphColumns G B) e := by
  ext i
  simp only [realVec,scaledColumns,Pi.smul_apply,smul_eq_mul,Rat.cast_mul,realColumns]

lemma scaledForm_cast (G : MultiGraph (d+1) m) (B : Finset (Fin m)) (s : Fin m → ℚ) :
    (scaledForm G B s).map (fun q : ℚ => (q:ℝ))=
      covariance (realColumns (graphColumns G B)) (realWeights s) := by
  ext i j
  simp only [scaledForm,covariance,map_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
    vecMulVec,weights,realColumns,realWeights,Rat.cast_sum,Rat.cast_mul,Rat.cast_pow,Matrix.of_apply]

lemma scaledColumns_leverage (G : MultiGraph (d+1) m) (B : Finset (Fin m))
    (s : Fin m → ℚ) (e : Fin m) :
    realVec (scaledColumns G B s) e ⬝ᵥ
      (((scaledForm G B s).map (fun q : ℚ => (q:ℝ)))⁻¹*ᵥrealVec (scaledColumns G B s) e)=
      leverage (realColumns (graphColumns G B)) (realWeights s) e := by
  rw [scaledColumns_cast,scaledForm_cast]
  simp only [leverage,realWeights,mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  ring

end AlgorithmicThinTrees.GraphicHalf
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Sparsification_GraphCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Graph certificates. -/

section

namespace AlgorithmicThinTrees.GraphicHalf
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open MetricTests Normalization RationalSigning
open scoped MatrixOrder
variable {n d m : ℕ}

lemma qform_outer (u x : Fin n → ℝ) : qform (vecMulVec u u) x=(u ⬝ᵥ x)^2 := by
  rw [qform,vecMulVec_mulVec,dotProduct_smul,op_smul_eq_smul,smul_eq_mul,dotProduct_comm x u,pow_two]

lemma cut_test (S : Finset (Fin n)) : Test (vecMulVec (cutIndicator S) (cutIndicator S)) := by
  refine ⟨ShortcutDual.outer_posSemidef _,?_⟩
  intro u v w
  simp only [qform_outer,eval_difference]
  rcases cutIndicator_binary S u with hu|hu <;>
    rcases cutIndicator_binary S v with hv|hv <;>
      rcases cutIndicator_binary S w with hw|hw <;> norm_num [hu,hv,hw]

lemma trace_mul_centered (D Z : Matrix (Fin n) (Fin n) ℝ) :
    (D*centered Z).trace=(centered D*Z).trace := by
  simp only [centered]
  rw [←Matrix.mul_assoc,←Matrix.mul_assoc,trace_mul_comm (D*centering n*Z),
    ←Matrix.mul_assoc (centering n)]
  simp only [Matrix.mul_assoc]

lemma centered_laplacian (G : MultiGraph n m) (A : Finset (Fin m)) :
    centered (G.laplacian A)=G.laplacian A := by
  apply centered_eq (G.laplacian_psd A).isHermitian
  simp only [laplacian,Matrix.sum_mulVec]
  apply sum_eq_zero
  intro e _
  rw [vecMulVec_mulVec]
  have he : G.incidence e ⬝ᵥ ones n=0 := by
    simp only [dotProduct,ones,mul_one]
    exact (mem_zeroSumSpace _).mp (G.incidence_zeroSum e)
  simp only [he,op_smul_eq_smul,zero_smul]

lemma centered_cut_trace (G : MultiGraph n m) (A : Finset (Fin m)) (S : Finset (Fin n)) :
    (G.laplacian A*centered (vecMulVec (cutIndicator S) (cutIndicator S))).trace=
      ((G.cut A S).card:ℝ) := by
  rw [trace_mul_centered,centered_laplacian,trace_mul_comm,ShortcutDual.trace_outer_mul]
  exact G.laplacian_cut A S

lemma cut_bound (G : MultiGraph n m) (hn : 0 < n) (A B : Finset (Fin m))
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : X ∈ metricDomain G)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hL : G.laplacian A ≤ (1/2:ℝ) • G.laplacian B+ε • regularize X)
    (S : Finset (Fin n)) :
    ((G.cut A S).card:ℝ) ≤ (1/2+3*ε)*(G.cut univ S).card := by
  let Z := centered (vecMulVec (cutIndicator S) (cutIndicator S))
  have hZ : CenteredTest Z := test_centered hn (cut_test S)
  have hh := trace_pairing_mono hL hZ.1.1
  simp only [Matrix.add_mul,Matrix.smul_mul,trace_add,trace_smul,smul_eq_mul,
    regularize_trace _ hZ] at hh
  have hx := hX.2.2.2 Z hZ
  have hcut : ((G.cut B S).card:ℝ) ≤ (G.cut univ S).card := by
    exact_mod_cast card_le_card (show G.cut B S ⊆ G.cut univ S from
      fun e he => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp he).2⟩)
  simp only [Z,centered_cut_trace] at hx hh
  have hm := mul_le_mul_of_nonneg_left hx hε
  nlinarith only [hh,hm,hcut]

lemma square_whitening {Q : Matrix (Fin d) (Fin d) ℝ} (hQ : Q.PosDef) :
    ∃M : Matrix (Fin d) (Fin d) ℝ, IsUnit M ∧ Mᵀ=M ∧ M*M=Q⁻¹ ∧ M*Q*M=1 := by
  obtain ⟨S,hS,hunit,hSS⟩ := posDef_sqrt_factors hQ
  have hSi : S⁻¹*S=1 := nonsing_inv_mul S ((isUnit_iff_isUnit_det _).mp hunit)
  have hiS : S*S⁻¹=1 := mul_nonsing_inv S ((isUnit_iff_isUnit_det _).mp hunit)
  refine ⟨S⁻¹,by simpa only [isUnit_nonsing_inv_iff] using hunit,?_,?_,?_⟩
  · rw [transpose_nonsing_inv,(isHermitian_iff_isSymm.mp hS).eq]
  · rw [←hSS,Matrix.mul_inv_rev]
  · rw [←hSS,←Matrix.mul_assoc,hSi,Matrix.one_mul,hiS]

lemma packing_bound (G : MultiGraph (d+1) m) (hn : 2 ≤ d+1)
    (B A : Finset (Fin m)) (hAB : A ⊆ B) (s : Fin m → ℚ)
    (hs : ∀e, 0 < s e)
    (hQ : ((scaledForm G B s).map (fun q : ℚ => (q:ℝ))).PosDef)
    {c h : ℝ} {r : ℕ} (hc : 0 < c) (hh : 0 < h) (hr : (r:ℝ)*h ≤ c)
    (hnorm : ∀e ∈ B, leverage (realColumns (graphColumns G B)) (realWeights s) e ≤ h)
    (hlow : c • ((scaledForm G B s).map (fun q : ℚ => (q:ℝ))) ≤
      StackedSigning.gram (realVec (scaledColumns G B s)) A) : G.TreePackable A r := by
  let Q := (scaledForm G B s).map (fun q : ℚ => (q:ℝ))
  obtain ⟨M,hM,hMt,hMM,hMQ⟩ := square_whitening hQ
  let L₀ := dropRoot d
  let L := L₀.trans (Matrix.toLinearEquiv' M hM.invertible)
  have hv (e : Fin m) (he : e ∈ B) : M*ᵥrealVec (scaledColumns G B s) e=
      (s e:ℝ) • L ⟨G.incidence e,G.incidence_zeroSum e⟩ := by
    rw [scaledColumns_cast,graphColumns_cast,ite_eq_left he,mulVec_smul]
    rfl
  have hvecnorm (e : Fin m) : (M*ᵥrealVec (scaledColumns G B s) e) ⬝ᵥ
      (M*ᵥrealVec (scaledColumns G B s) e)=
        leverage (realColumns (graphColumns G B)) (realWeights s) e := by
    rw [←hMt,GramWhitening.rectangular_norm,hMt,hMM,scaledColumns_leverage]
  have hLo := GramWhitening.congruence_mono hlow M
  rw [hMt,Matrix.mul_smul,Matrix.smul_mul,hMQ] at hLo
  have hGram : M*StackedSigning.gram (realVec (scaledColumns G B s)) A*M=
      ∑e∈A,vecMulVec ((s e:ℝ) • L ⟨G.incidence e,G.incidence_zeroSum e⟩)
        ((s e:ℝ) • L ⟨G.incidence e,G.incidence_zeroSum e⟩) := by
    rw [StackedSigning.gram]
    nth_rw 1 [←hMt]
    rw [←GramWhitening.congruence_sum_outer,hMt]
    apply sum_congr rfl
    intro e he
    rw [hv e (hAB he)]
  rw [hGram] at hLo
  apply G.represented_frame_treePackable hn L (fun e => (s e:ℝ))
    (fun e => by exact_mod_cast hs e) A hc hh hr
  · intro e he
    dsimp only
    rw [←hv e (hAB he),hvecnorm]
    exact hnorm e (hAB he)
  · intro x
    have hx := qform_mono hLo x
    change qform (c • (1 : Matrix (Fin d) (Fin d) ℝ)) x ≤ qform _ x at hx
    rw [qform_smul,qform_covariance] at hx
    simpa only [qform,one_mulVec] using hx

end AlgorithmicThinTrees.GraphicHalf
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Sparsification_ShortcutExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Shortcut extraction. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped MatrixOrder
variable {n m : ℕ}

lemma rounding_absorbed (r : ℕ) (hr : 1 ≤ r) : 1 ≤ (r:ℝ)^(-1/16:ℝ)*r := by
  have hp : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have he : (r:ℝ)^(-1/16:ℝ)*r=(r:ℝ)^(15/16:ℝ) := by
    conv_lhs => arg 2; rw [←Real.rpow_one (r:ℝ)]
    rw [←Real.rpow_add hp]
    norm_num
  rw [he]
  exact Real.one_le_rpow (by exact_mod_cast hr) (by norm_num)

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Sparsification_HalfNumeric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Half numeric. -/

section

namespace AlgorithmicThinTrees.GraphicHalf
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open MetricTests MetricTests.RationalStep Normalization RationalSigning Filter Topology
open scoped MatrixOrder

lemma countError_bounds (r : ℕ) (hr : 0 < r) :
    errorU r ≤ (countError r:ℝ) ∧ (countError r:ℝ) ≤ 2*errorU r := by
  have hroot := nthRoot_le_real_root 16 r (by norm_num)
  have hr0 : 0 < (r:ℝ) := Nat.cast_pos.mpr hr
  have hu1 : (1:ℝ) ≤ Nat.nthRoot 16 r := by exact_mod_cast nthRoot_pos 16 r (by norm_num) hr
  have hup := real_root_lt_nthRoot_add 16 r (by norm_num)
  have hp : 0 < (r:ℝ)^(1/16:ℝ) := Real.rpow_pos_of_pos hr0 _
  have he : errorU r=1/((r:ℝ)^(1/16:ℝ)) := by
    simp only [errorU,show (-1/16:ℝ)= -(1/16:ℝ) by ring,Real.rpow_neg hr0.le,one_div]
  simp only [Nat.cast_ofNat] at hroot hup
  rw [he]
  have hg : (countError r:ℝ)=1/(Nat.nthRoot 16 r:ℝ) := by simp [countError]
  rw [hg]
  constructor
  · exact one_div_le_one_div_of_le (by linarith only [hu1]) hroot
  · have hu0 : 0 < (Nat.nthRoot 16 r:ℝ) := by linarith only [hu1]
    apply (div_le_iff₀ hu0).mpr
    rw [show 2*(1/((r:ℝ)^(1/16:ℝ)))*(Nat.nthRoot 16 r:ℝ)=
      (2*(Nat.nthRoot 16 r:ℝ))/((r:ℝ)^(1/16:ℝ)) by ring]
    apply (le_div_iff₀ hp).mpr
    linarith only [hu1,hup]

lemma eventual_numeric : ∀r : ℕ, 2^2048 ≤ r → Numeric r :=
  fun r hr => Q339.Numeric.numeric_explicit r hr

lemma rounding_bounds {r : ℕ} (hn : Numeric r) :
    ((1/2:ℝ)-17*errorU r)*r ≤ nextCount r ∧
    (nextCount r:ℝ) ≤ ((1/2:ℝ)-8*errorU r)*r := by
  have hr0 : 0 < r := by have := hn.rlarge;omega
  have hrR : (0:ℝ) < r := Nat.cast_pos.mpr hr0
  have hu := errorU_nonneg r
  obtain ⟨hv,hv2⟩ := countError_bounds r hr0
  have hsmall := hn.small
  have hnonneg : 0 ≤ (1-16*countError r)*(r:ℚ)/2 := by
    have hh : (0:ℝ) ≤ (1-16*(countError r:ℝ))*(r:ℝ)/2 := by positivity [show 0 ≤ 1-16*(countError r:ℝ) by linarith only [hv2,hsmall]]
    exact_mod_cast hh
  have hlo := Nat.sub_one_lt_floor ((1-16*countError r)*(r:ℚ)/2)
  have hhi := Nat.floor_le hnonneg
  have hloR : (1-16*(countError r:ℝ))*(r:ℝ)/2-1 < (nextCount r:ℝ) := by exact_mod_cast hlo
  have hhiR : (nextCount r:ℝ) ≤ (1-16*(countError r:ℝ))*(r:ℝ)/2 := by exact_mod_cast hhi
  have hru := rounding_absorbed r (by omega)
  change 1 ≤ errorU r*r at hru
  constructor
  · have hm := mul_le_mul_of_nonneg_right hv2 hrR.le
    nlinarith only [hloR,hm,hru]
  · have hm := mul_le_mul_of_nonneg_right hv hrR.le
    nlinarith only [hhiR,hm]

lemma nextCount_bounds {r : ℕ} (hn : Numeric r) :
    (r:ℝ)/4 ≤ nextCount r ∧ (nextCount r:ℝ) ≤ (r:ℝ)/2 ∧ 0 < nextCount r := by
  obtain ⟨hlo,hhi⟩ := rounding_bounds hn
  have hu := errorU_nonneg r
  have hsmall := hn.small
  have hr0 : (0:ℝ) < r := by exact_mod_cast (show 0 < r by have := hn.rlarge;omega)
  have hm := mul_le_mul_of_nonneg_right hsmall hr0.le
  have hz := mul_nonneg hu hr0.le
  have hpos : (0:ℝ) < nextCount r := by nlinarith only [hlo,hm,hr0]
  exact ⟨by nlinarith only [hlo,hm],by nlinarith only [hhi,hz],by exact_mod_cast hpos⟩

lemma packing_numeric {r q : ℕ} (hn : Numeric r) (hq : 0 < q)
    (hqr : (1-6*errorU r)*(r:ℝ) ≤ q) :
    (nextCount r:ℝ)*((1+4/(r:ℝ))/(q:ℝ)) ≤ 1/2-halfError r := by
  have hr0 : (0:ℝ) < r := by exact_mod_cast (show 0 < r by have := hn.rlarge;omega)
  have hq0 : (0:ℝ) < q := Nat.cast_pos.mpr hq
  have hu := errorU_nonneg r
  have herror0 : 0 ≤ halfError r := by unfold halfError; positivity
  have hc : 0 ≤ 1/2-halfError r := by linarith only [hn.loss,hn.small]
  rw [←mul_div_assoc,div_le_iff₀ hq0]
  have hupper := (rounding_bounds hn).2
  have hsize := mul_le_mul_of_nonneg_left hn.inverse (Nat.cast_nonneg (nextCount r) : (0:ℝ) ≤ _)
  have htarg := mul_le_mul_of_nonneg_left hqr hc
  have hm := mul_le_mul_of_nonneg_right hupper (by linarith only [hu] : 0 ≤ 1+errorU r)
  have hp : 0 ≤ (1-6*errorU r)*(r:ℝ) := mul_nonneg (by linarith only [hn.small]) hr0.le
  have hloss := mul_le_mul_of_nonneg_right hn.loss hp
  have husq := mul_nonneg (sq_nonneg (errorU r)) hr0.le
  have huR := mul_nonneg hu hr0.le
  nlinarith only [hsize,htarg,hm,hloss,husq,huR]

lemma half_ratio {r : ℕ} (hn : Numeric r) :
    (1/2+3*halfError r)*(r:ℝ) ≤ (1+80*errorU r)*nextCount r := by
  have hrR := (Nat.cast_nonneg r : (0:ℝ) ≤ r)
  have hu := errorU_nonneg r
  have hlo := (rounding_bounds hn).1
  have hB : 0 ≤ 20-1360*errorU r := by linarith only [hn.small]
  have hpos := mul_nonneg (mul_nonneg hu hB) hrR
  have hm := mul_le_mul_of_nonneg_left hlo (by linarith only [hu] : 0 ≤ 1+80*errorU r)
  have he := mul_le_mul_of_nonneg_right hn.loss hrR
  nlinarith only [hm,hpos,he]

lemma normalized_size {r q : ℕ} (hn : Numeric r)
    (hqr : (1-6*errorU r)*(r:ℝ) ≤ q) :
    (1+4/(r:ℝ))/(q:ℝ) ≤ 4*(r:ℝ)^(-1/4:ℝ) := by
  have hr0 : (0:ℝ) < r := by exact_mod_cast (show 0 < r by have := hn.rlarge;omega)
  have hqR : (r:ℝ)/2 ≤ q := by
    have hm := mul_le_mul_of_nonneg_right hn.small hr0.le
    nlinarith only [hqr,hm]
  have hq0 : (0:ℝ) < q := by linarith only [hqR,hr0]
  have hi : (1+4/(r:ℝ))/(q:ℝ) ≤ 4/(r:ℝ) := by
    have hupp : 1+4/(r:ℝ) ≤ 2 := by linarith only [hn.inverse,hn.small]
    rw [div_le_div_iff₀ hq0 hr0]
    have hm := mul_le_mul_of_nonneg_right hupp hr0.le
    nlinarith only [hm,hqR]
  have hpow := Real.rpow_le_rpow_of_exponent_le
    (show (1:ℝ) ≤ r by exact_mod_cast (show 1 ≤ r by have := hn.rlarge;omega))
    (by norm_num : (-1:ℝ) ≤ -1/4)
  simp only [Real.rpow_neg_one] at hpow
  apply hi.trans
  simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hpow (by norm_num : (0:ℝ) ≤ 4)

end AlgorithmicThinTrees.GraphicHalf
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Sparsification_Step
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparsification step. -/

section

namespace AlgorithmicThinTrees.GraphicHalf
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open MetricTests MetricTests.RationalStep Normalization RationalSigning
open scoped MatrixOrder
variable {d m : ℕ}

theorem sparsification_correct_explicit_oai : ∀r : ℕ, 2^2048 ≤ r →
    ∀(d m : ℕ) (G : MultiGraph (d+1) m), 2 ≤ d+1 → G.TreePackable univ r →
      (r:ℝ)/4 ≤ nextCount r ∧ (nextCount r:ℝ) ≤ (r:ℝ)/2 ∧ 0 < nextCount r ∧
      G.TreePackable (sparsify G r) (nextCount r) ∧
      (∀S : Finset (Fin (d+1)), ((G.cut (sparsify G r) S).card:ℝ) ≤
        (1/2+3*halfError r)*(G.cut univ S).card) ∧
      (1/2+3*halfError r)*(r:ℝ) ≤ (1+80*errorU r)*nextCount r := by
  have hstep := shortcut_correct_explicit
  have hnum := eventual_numeric
  intro r hr d m G hn hp
  have hr₁ := hr
  have hr₂ := hr
  have hnumer := hnum r hr₂
  have hr0 : 0 < r := by have := hnumer.rlarge; omega
  have hconn := packing_connected G hr0 hp
  obtain ⟨hX,hpack,hqpos,hqr,hqbound,hres⟩ := hstep r hr₁ (d+1) m G hn hp
  let a := extractState G r
  let B := a.active
  let q := a.packingTarget
  let s := normalizedScales q r (graphColumns G B)
  have hX' : a.realMatrix ∈ metricDomain G := hX
  have hqr' : (1-6*errorU r)*(r:ℝ) ≤ q := hqbound
  obtain ⟨hs,hleverage,hbits⟩ := graphic_normalization G B hqpos hqr hpack
  change (∀e, 0 < s e ∧ s e ≤ 1) at hs
  change (∀e, leverage (realColumns (graphColumns G B)) (realWeights s) e ≤ (1+4/(r:ℝ))/(q:ℝ)) at hleverage
  have hQ : ((scaledForm G B s).map (fun x : ℚ => (x:ℝ))).PosDef := by
    rw [scaledForm_cast]
    obtain ⟨F⟩ := graph_containedPacking G B hqpos hpack
    exact F.covariance_posDef _ (realWeights_box hs).1
  have hnorm : ∀e, realVec (fullColumns G B) e ⬝ᵥ
      (((positiveForm a.matrix).map (fun x : ℚ => (x:ℝ)))⁻¹*ᵥrealVec (fullColumns G B) e)+
      leverage (realColumns (graphColumns G B)) (realWeights s) e ≤ varianceBound r := by
    intro e
    have hlev := (hleverage e).trans (normalized_size hnumer hqr')
    have hfirst : realVec (fullColumns G B) e ⬝ᵥ
        (((positiveForm a.matrix).map (fun x : ℚ => (x:ℝ)))⁻¹*ᵥrealVec (fullColumns G B) e) ≤
        (r:ℝ)^(-1/4:ℝ) := by
      rw [fullColumns_cast,positiveForm_cast]
      by_cases he : e ∈ B
      · rw [ite_eq_left he]
        exact hres e he
      · rw [ite_eq_right he,zero_dotProduct]
        exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    unfold varianceBound
    linarith only [hfirst,hlev]
  obtain ⟨hlap,hframe⟩ := half_bounds G B a.matrix s hconn hX' hQ
    (show 0 ≤ varianceBound r by unfold varianceBound; positivity) hnorm
  change G.laplacian (sparsify G r) ≤ (1/2:ℝ) • G.laplacian B+
    halfError r • regularize a.realMatrix at hlap
  change (1/2-halfError r) • (scaledForm G B s).map (fun x : ℚ => (x:ℝ)) ≤
    StackedSigning.gram (realVec (scaledColumns G B s)) (sparsify G r) at hframe
  obtain ⟨hlo,hhi,hpos⟩ := nextCount_bounds hnumer
  refine ⟨hlo,hhi,hpos,?_,?_,half_ratio hnumer⟩
  · apply packing_bound G hn B (sparsify G r) inter_subset_right s (fun e => (hs e).1) hQ
      (c:=1/2-halfError r) (h:=(1+4/(r:ℝ))/(q:ℝ))
    · linarith only [hnumer.loss,hnumer.small]
    · positivity
    · exact packing_numeric hnumer hqpos hqr'
    · intro e _; exact hleverage e
    · exact hframe
  · intro S
    exact cut_bound G (by omega) (sparsify G r) B hX'
      (by unfold halfError; positivity) hlap S

end AlgorithmicThinTrees.GraphicHalf
end

end OAI
end

theorem solution : type_of% @OAI.AlgorithmicThinTrees.GraphicHalf.sparsification_correct_explicit_oai := @OAI.AlgorithmicThinTrees.GraphicHalf.sparsification_correct_explicit_oai

