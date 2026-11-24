-- Prove2me | solution 1 for GlobalTheory.locRes_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:19:08.571727+00:00
-- url     : https://prove2.me/submissions/6aacb900-db1b-4d8e-9a94-1e5b84f9d659

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
universe v u
open GlobalTheory
variable {ι : Type} {R : Type u} [CommRing R]
variable (f : ι → R) (M : Type v) [AddCommGroup M] [Module R M]
namespace GlobalTheory
theorem _root_.solution {s t : Finset ι} (h : s ⊆ t) (m : M) (a : Submonoid.powers (∏ i ∈ s, f i))
    (b : Submonoid.powers (∏ i ∈ t, f i)) (c : R) (hb : (b : R) = c * a) :
    locRes f M h (LocalizedModule.mk m a) = LocalizedModule.mk (c • m) b := by
  apply IsLocalizedModule.smul_injective (LocalizedModule.mkLinearMap _ M) b
  have h1 : (a : R) • LocalizedModule.mk m a = LocalizedModule.mk m 1 := by
    rw [LocalizedModule.smul'_mk]; exact LocalizedModule.mk_cancel a m
  have h2 : (b : R) • LocalizedModule.mk (c • m) b = LocalizedModule.mk (c • m) 1 := by
    rw [LocalizedModule.smul'_mk]; exact LocalizedModule.mk_cancel b _
  simp only [Submonoid.smul_def]
  rw [h2, hb, mul_smul, ← map_smul, h1, locRes_mk_one, LocalizedModule.smul'_mk]
end GlobalTheory
