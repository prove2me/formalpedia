-- Prove2me | solution 1 for GlobalTheory.smul_away_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:51:39.522547+00:00
-- url     : https://prove2.me/submissions/b9288adc-20e6-47cc-95f3-e8bc1ebf5304

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsGradedMapLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Theorems.Thm_GlobalTheory_isUnit_away_of_dvd_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open DirectSum MvPolynomial CategoryTheory
universe u
noncomputable section
open GlobalTheory
open GradedHilbert
variable {A : Type*} [CommRing A] (M : Type*) [AddCommGroup M] [Module A M]
  {N : Type*} [AddCommGroup N] [Module A N] {P : Type*} [AddCommGroup P] [Module A P]
variable {M}
namespace GlobalTheory
theorem _root_.solution {f g : A} {k : ℕ} (h : f ∣ g ^ k) :
    Function.Bijective (LinearMap.lsmul A (LocalizedModule.Away g M) f) :=
  (Module.End.isUnit_iff _).1 (isUnit_away_of_dvd_pow h)
end GlobalTheory
