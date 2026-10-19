-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriInvalidRows.orthogonalJacobiTrudiDimension_lowered_eq_zero_of_not_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:45.453197+00:00
-- url     : https://prove2.me/submissions/7d69740a-6e85-41e5-b133-6aa370bba1d9

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankOrthogonalTensorPieriCoefficient_orthogonalTensorPieriCoefficient_eq_matrix

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option maxHeartbeats 1800000
open MetricCodes
open MetricCodes.Spherical
noncomputable section
set_option autoImplicit false
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriInvalidRows
open MetricCodes.Spherical.HigherWeylBinomialDeterminant
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriCoefficient
namespace MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriInvalidRows
theorem _root_.solution
    {r : ℕ} (n : ℕ) {lam : Fin (r + 1) → ℕ}
    (hlam : Antitone lam) (i : Fin (r + 1))
    (hbad : ¬ Antitone (loweredInternalYoungWeight lam i)) :
    orthogonalJacobiTrudiDimension n (loweredInternalYoungWeight lam i) = 0 := by
  classical
  have hviol : ∃ j : Fin r,
      loweredInternalYoungWeight lam i j.castSucc <
        loweredInternalYoungWeight lam i j.succ := by
    have hnot : ¬ ∀ j : Fin r,
        loweredInternalYoungWeight lam i j.succ ≤
          loweredInternalYoungWeight lam i j.castSucc := by
      intro h
      exact hbad (Fin.antitone_iff_succ_le.mpr h)
    push Not at hnot
    exact hnot
  obtain ⟨j, hlt⟩ := hviol
  have hdom := hlam (Fin.castSucc_le_succ j)
  have hji : j.castSucc = i := by
    by_contra hcast
    by_cases hsucc : j.succ = i
    · subst i
      simp [loweredInternalYoungWeight, hcast] at hlt
      omega
    · simp [loweredInternalYoungWeight, hcast, hsucc] at hlt
      omega
  subst i
  have hne : j.castSucc ≠ j.succ := ne_of_lt Fin.castSucc_lt_succ
  have hne' : j.succ ≠ j.castSucc := Ne.symm hne
  have hpos : 0 < lam j.castSucc := by
    simp [loweredInternalYoungWeight, hne'] at hlt
    omega
  have heq : lam j.castSucc = lam j.succ := by
    simp [loweredInternalYoungWeight, hne'] at hlt
    omega
  unfold orthogonalJacobiTrudiDimension
  apply Matrix.det_zero_of_row_eq hne
  funext k
  rw [orthogonalTensorPieriCoefficient_eq_matrix,
    orthogonalTensorPieriCoefficient_eq_matrix]
  have hshift :
      ((loweredInternalYoungWeight lam j.castSucc j.castSucc : ℤ) -
          (j.castSucc.val : ℤ)) =
        ((loweredInternalYoungWeight lam j.castSucc j.succ : ℤ) -
          (j.succ.val : ℤ)) := by
    simp [loweredInternalYoungWeight, hne']
    rw [Nat.cast_sub (show 1 ≤ lam j.castSucc by omega)]
    push_cast
    have heq' : (lam j.castSucc : ℤ) = (lam j.succ : ℤ) := by
      exact_mod_cast heq
    omega
  rw [hshift]
end MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriInvalidRows
