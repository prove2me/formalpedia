-- Prove2me | solution 2 for GlobalTheory.CompanionTheory.SW.Primes.summable_one_div_absNorm_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:41:14.483948+00:00
-- url     : https://prove2.me/submissions/26c7c4da-1194-4b36-9c6f-472c02ccb2e8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SummableOneDivAbsNormSq
import Theorems.Thm_ReciprocityTheory_Cheb_summable_absNorm_rpow_ideal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Primes
namespace GlobalTheory.CompanionTheory.SW.Primes
theorem _root_.solution :
    ∀ (F : Type) [Field F] [NumberField F],
      Summable fun v : HeightOneSpectrum (𝓞 F) => 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2 := by
  intro F _ _
  have h := (ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal F (s := 2) (by norm_num)).comp_injective
    (i := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal) (fun _ _ h => HeightOneSpectrum.ext h)
  refine h.congr fun v => ?_
  simp only [Function.comp_apply]
  rw [Real.rpow_neg (Nat.cast_nonneg _), one_div]
  norm_num
end GlobalTheory.CompanionTheory.SW.Primes
