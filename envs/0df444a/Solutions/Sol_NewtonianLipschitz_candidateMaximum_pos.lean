-- Prove2me | solution 1 for NewtonianLipschitz.candidateMaximum_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:55:39.36156+00:00
-- url     : https://prove2.me/submissions/adb89762-51f3-44b8-affc-ddb17d3d9df3

module
public import Definitions.Def_NewtonianLipschitz_AdmissibleCriticalDirection
public import Definitions.Def_NewtonianLipschitz_AdmissibleSecantPairs
public import Theorems.Thm_NewtonianLipschitz_candidateCoefficient_eq
public import Theorems.Thm_NewtonianLipschitz_candidateCoefficient_le_at_criticalPoint
public import Theorems.Thm_NewtonianLipschitz_candidateMaximum_eq


set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution : 0 < candidateMaximum := by
  have h0 : candidateCoefficient (0 : ℝ) ≤ candidateMaximum := by
    rw [candidateMaximum_eq]
    exact candidateCoefficient_le_at_criticalPoint (0 : ℝ)
      ⟨by norm_num, by norm_num⟩
  have hv : candidateCoefficient (0 : ℝ) = 2 := by
    rw [candidateCoefficient_eq]
    norm_num
  rw [hv] at h0
  linarith
end NewtonianLipschitz
