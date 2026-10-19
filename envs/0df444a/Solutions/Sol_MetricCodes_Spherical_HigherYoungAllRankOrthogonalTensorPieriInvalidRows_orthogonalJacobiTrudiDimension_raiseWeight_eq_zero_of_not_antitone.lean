-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriInvalidRows.orthogonalJacobiTrudiDimension_raiseWeight_eq_zero_of_not_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:45.453197+00:00
-- url     : https://prove2.me/submissions/ed303d64-22ba-456d-b356-3103aa96d318

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
    (hbad : ¬ Antitone (raiseWeight lam i)) :
    orthogonalJacobiTrudiDimension n (raiseWeight lam i) = 0 := by
  classical
  have hviol : ∃ j : Fin r,
      raiseWeight lam i j.castSucc < raiseWeight lam i j.succ := by
    have hnot : ¬ ∀ j : Fin r,
        raiseWeight lam i j.succ ≤ raiseWeight lam i j.castSucc := by
      intro h
      exact hbad (Fin.antitone_iff_succ_le.mpr h)
    push Not at hnot
    exact hnot
  obtain ⟨j, hlt⟩ := hviol
  have hdom := hlam (Fin.castSucc_le_succ j)
  have hji : j.succ = i := by
    by_contra hsucc
    by_cases hcast : j.castSucc = i
    · subst i
      simp [raiseWeight, hsucc] at hlt
      omega
    · simp [raiseWeight, hcast, hsucc] at hlt
      omega
  subst i
  have hne : j.castSucc ≠ j.succ := ne_of_lt Fin.castSucc_lt_succ
  have heq : lam j.castSucc = lam j.succ := by
    simp [raiseWeight, hne] at hlt
    omega
  unfold orthogonalJacobiTrudiDimension
  apply Matrix.det_zero_of_row_eq hne
  funext k
  rw [orthogonalTensorPieriCoefficient_eq_matrix,
    orthogonalTensorPieriCoefficient_eq_matrix]
  have hshift :
      ((raiseWeight lam j.succ j.castSucc : ℤ) -
          (j.castSucc.val : ℤ)) =
        ((raiseWeight lam j.succ j.succ : ℤ) -
          (j.succ.val : ℤ)) := by
    simp [raiseWeight, hne, heq]
  rw [hshift]
end MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriInvalidRows
