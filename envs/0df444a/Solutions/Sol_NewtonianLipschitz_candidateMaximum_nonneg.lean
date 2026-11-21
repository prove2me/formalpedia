-- Prove2me | solution 1 for NewtonianLipschitz.candidateMaximum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:43:25.928825+00:00
-- url     : https://prove2.me/submissions/f37b3635-918a-496f-a6fa-de9b0d9ad01f

module
public import Definitions.Def_NewtonianLipschitz_JacobianSignedBounds
public import Definitions.Def_NewtonianLipschitz_JacobianCartesianBound
public import Theorems.Thm_NewtonianLipschitz_candidateCoefficient_eq
public import Theorems.Thm_NewtonianLipschitz_candidateCoefficient_le_at_criticalPoint
public import Theorems.Thm_NewtonianLipschitz_candidateMaximum_eq


set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution : 0 ≤ candidateMaximum := by
  have h0 :
      candidateCoefficient (0 : ℝ) ≤ candidateMaximum := by
    rw [candidateMaximum_eq]
    exact candidateCoefficient_le_at_criticalPoint (0 : ℝ)
      ⟨by norm_num, by norm_num⟩
  have hvalue : candidateCoefficient (0 : ℝ) = 2 := by
    rw [candidateCoefficient_eq]
    norm_num
  rw [hvalue] at h0
  linarith
end NewtonianLipschitz
