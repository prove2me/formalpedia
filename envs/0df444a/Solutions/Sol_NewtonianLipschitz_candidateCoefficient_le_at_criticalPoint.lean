-- Prove2me | solution 1 for NewtonianLipschitz.candidateCoefficient_le_at_criticalPoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:41:52.138879+00:00
-- url     : https://prove2.me/submissions/8e9216e8-1dc9-479e-8230-c22a0b0db44a

module
public import Definitions.Def_NewtonianLipschitz_CubicCandidate
public import Definitions.Def_NewtonianLipschitz_ScalarMaximum
public import Theorems.Thm_NewtonianLipschitz_candidateCoefficient_hasDerivAt
public import Theorems.Thm_NewtonianLipschitz_stationaryCubic_positive_before_root
public import Theorems.Thm_NewtonianLipschitz_stationaryCubic_negative_after_root

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    candidateCoefficient t ≤
      candidateCoefficient candidateCriticalPoint := by
  have hmax :
      IsMaxOn candidateCoefficient (Set.Icc (0 : ℝ) 1)
        candidateCriticalPoint := by
    apply isMaxOn_Icc_of_deriv
    · exact (candidateCoefficient_hasDerivAt 0).continuousAt
    · exact (candidateCoefficient_hasDerivAt candidateCriticalPoint).continuousAt
    · exact (candidateCoefficient_hasDerivAt 1).continuousAt
    · intro x hx
      exact (candidateCoefficient_hasDerivAt x).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (candidateCoefficient_hasDerivAt x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(candidateCoefficient_hasDerivAt x).deriv]
      have hp : 0 < stationaryCubic x :=
        stationaryCubic_positive_before_root x (le_of_lt hx.1) hx.2
      exact div_nonneg
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) hp.le)
        (pow_nonneg (Real.sqrt_nonneg _) _)
    · intro x hx
      rw [(candidateCoefficient_hasDerivAt x).deriv]
      have hp : stationaryCubic x < 0 :=
        stationaryCubic_negative_after_root x hx.1 (le_of_lt hx.2)
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos
          (by norm_num : (0 : ℝ) ≤ 6) hp.le)
        (pow_nonneg (Real.sqrt_nonneg _) _)
  exact hmax ht
end NewtonianLipschitz
