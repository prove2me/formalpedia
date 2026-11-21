-- Prove2me | solution 1 for NewtonianLipschitz.candidateMaximum_ge_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:55:42.688355+00:00
-- url     : https://prove2.me/submissions/09d7221f-e0f2-49d7-b8a4-7fb5192961c0

module
public import Definitions.Def_NewtonianLipschitz_AdmissibleSecantPairs
public import Definitions.Def_NewtonianLipschitz_LongSeparation
public import Theorems.Thm_NewtonianLipschitz_candidateCoefficient_eq
public import Theorems.Thm_NewtonianLipschitz_candidateCoefficient_le_at_criticalPoint
public import Theorems.Thm_NewtonianLipschitz_candidateMaximum_eq


set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution : (2 : ℝ) ≤ candidateMaximum := by
  have hmax :=
    candidateCoefficient_le_at_criticalPoint (0 : ℝ)
      (by constructor <;> norm_num : (0 : ℝ) ∈ Set.Icc 0 1)
  have hzero : candidateCoefficient (0 : ℝ) = 2 := by
    rw [candidateCoefficient_eq]
    norm_num
  rw [hzero] at hmax
  rwa [candidateMaximum_eq]
end NewtonianLipschitz
