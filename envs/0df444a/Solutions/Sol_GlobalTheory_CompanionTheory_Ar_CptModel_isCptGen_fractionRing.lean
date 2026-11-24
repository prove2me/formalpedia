-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CptModel.isCptGen_fractionRing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:49:46.269646+00:00
-- url     : https://prove2.me/submissions/424c6d10-abb0-46dd-b098-f70f7cc64e34

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_genMap_self
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_mem_regAt_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_genMap_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.CptModel
open AlgebraicGeometry CategoryTheory
variable {R K : Type} [CommRing R] [Field K]
namespace GlobalTheory.CompanionTheory.Ar.CptModel
theorem _root_.solution [IsDomain R] [Algebra R K] [IsFractionRing R K] :
    IsCptGen (pt (algebraMap R K)) := by
  have hi := IsFractionRing.injective R K
  refine ⟨?_, genMap_injective _ hi⟩
  rw [← genMap_self]
  refine ⟨genMap_injective _ hi _, fun c => ?_⟩
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := R) c
  have h0 : algebraMap R K s ≠ 0 := (map_ne_zero_iff _ hi).2 (nonZeroDivisors.ne_zero hs)
  refine (mem_regAt_iff _ (self _) _).2 ⟨a, s, ?_, h0, div_mul_cancel₀ _ h0⟩
  change s ∉ (genPt (pt (algebraMap R K))).asIdeal
  rw [genPt_asIdeal]
  exact h0
end GlobalTheory.CompanionTheory.Ar.CptModel
