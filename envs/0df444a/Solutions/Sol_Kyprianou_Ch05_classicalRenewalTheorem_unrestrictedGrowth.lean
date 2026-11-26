-- Prove2me | solution 1 for Kyprianou.Ch05.classicalRenewalTheorem_unrestrictedGrowth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:06:27.955419+00:00
-- url     : https://prove2.me/submissions/3dbf55f9-8895-4e77-bd6c-1f242a64506f

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_renewal_cdf_monotone
import Theorems.Thm_SmithRenewal_Elementary_elementary_renewal_theorem
import Theorems.Thm_Kyprianou_Ch05_smithFiniteMeanCompatibility
import Theorems.Thm_Kyprianou_Ch05_smithIIDRealisation
import Theorems.Thm_Kyprianou_Ch05_smithEpochConvolutionLaw
import Theorems.Thm_Kyprianou_Ch05_smithRenewalMassFromEpochLaws
import Theorems.Thm_Kyprianou_Ch05_smithRenewalRatioTransfer
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05 SmithRenewal.Elementary

/-- Transfer Smith's elementary renewal limit to the convolution measure. -/
theorem solution
    (F : Measure Real) [IsProbabilityMeasure F]
    (hSupport : F (Set.Iio (0 : Real)) = 0)
    (hFiniteMean : Integrable (fun x : Real => x) F)
    (hPositiveMean : 0 < ∫ x : Real, x ∂F) :
    let mu := ∫ x : Real, x ∂F
    let V := renewalMeasure F
    (Tendsto
       (fun x : Real => (V (Set.Icc (0 : Real) x)).toReal / x)
       atTop (nhds (1 / mu))) := by
  dsimp only
  obtain ⟨P, X, hP, hX, hLaw⟩ := smithIIDRealisation F hSupport hPositiveMean
  letI := hP
  have hmu : mu1 X P = ENNReal.ofReal (∫ x : Real, x ∂F) := by
    rw [← smithFiniteMeanCompatibility F hSupport hFiniteMean]
    unfold mu1 SmithRegenerative.Equilibrium.mean
    rw [← hLaw 0, lintegral_map ENNReal.measurable_ofReal (hX.measurable 0)]
  have hlim := elementary_renewal_theorem P X hX
  rw [hmu] at hlim
  exact smithRenewalRatioTransfer
    (fun t => renewalMeasure F (Set.Icc 0 t)) (H X P)
    (∫ x : Real, x ∂F) hPositiveMean
    (fun t ht => smithRenewalMassFromEpochLaws P X F hX
      (smithEpochConvolutionLaw P X F hX hLaw) t ht) hlim
