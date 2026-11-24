-- Prove2me | solution 1 for GlobalTheory.isUnit_away_of_dvd_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:45:39.178823+00:00
-- url     : https://prove2.me/submissions/cedcd719-aacc-4cfa-8793-e13527820b4d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsGradedMapLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc

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
    IsUnit (algebraMap A (Module.End A (LocalizedModule.Away g M)) f) :=
  isUnit_algebraMap_end_of_dvd h (IsLocalizedModule.map_units
    (LocalizedModule.mkLinearMap (Submonoid.powers g) M) (⟨g ^ k, k, rfl⟩ : Submonoid.powers g))
end GlobalTheory
