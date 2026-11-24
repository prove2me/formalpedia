-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FlDecomp.isLat_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:31:32.412028+00:00
-- url     : https://prove2.me/submissions/cec390c4-3367-40e5-ad62-e2d714ec87c8

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfFrameWittTorus
import Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_mem_pull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FlDecomp
open CompanionTheory.Rg.FlB
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
namespace GlobalTheory.CompanionTheory.FlDecomp
theorem _root_.solution (k : V ≃ₗ[L] V) {Λ : AddSubgroup V} (hΛ : IsLat L Λ) : IsLat L (pull k Λ) := by
  obtain ⟨m, b, hb⟩ := hΛ
  refine ⟨m, b.map k.symm, fun x => ?_⟩
  rw [mem_pull, hb]
  simp [Module.Basis.map_repr]
end GlobalTheory.CompanionTheory.FlDecomp
