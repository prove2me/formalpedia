-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FrameTorus.stTor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:09:34.913484+00:00
-- url     : https://prove2.me/submissions/3148ba17-e799-4adc-aa62-323f86da5631

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TorusStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FrameTorus_span_gens
import Theorems.Thm_GlobalTheory_CompanionTheory_FrameTorus_pair_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_FrameTorus_tor_e
import Theorems.Thm_GlobalTheory_CompanionTheory_FrameTorus_tor_f
import Theorems.Thm_GlobalTheory_CompanionTheory_FrameTorus_tor_w
import Theorems.Thm_GlobalTheory_CompanionTheory_FrameTorus_tor_inv
import Theorems.Thm_GlobalTheory_CompanionTheory_FrameTorus_tor_iso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CompanionTheory.FrameTorus.pair_apply

set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FrameTorus
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
namespace GlobalTheory.CompanionTheory.FrameTorus
theorem _root_.solution : StTor := by
  unfold StTor ForAll
  intro L _ _ _ _ s hs δ hδ V _ _ _ h hH l e f W hF u hu
  have hδ0 : δ ≠ 0 := hδ.1
  have hui : ∀ i, (u i)⁻¹ ≠ 0 := fun i => inv_ne_zero (hu i)
  let t : V ≃ₗ[L] V := LinearEquiv.ofLinear (tor hH δ e f u) (tor hH δ e f fun i => (u i)⁻¹)
    (tor_inv hH hF hδ0 u hu)
    (by simpa using tor_inv hH hF hδ0 (fun i => (u i)⁻¹) hui)
  refine ⟨t, fun x y => tor_iso hs.1 hH hF hδ0 u hu x y, ⟨fun i => tor_e hH hF hδ0 u i,
    fun i => tor_f hH hF hδ0 u i, fun w hw => tor_w hH hF u hw⟩, ?_⟩
  rintro t' ⟨h1, h2, h3⟩
  apply LinearEquiv.toLinearMap_injective
  refine LinearMap.ext_on (span_gens hF) ?_
  rintro x ((⟨i, rfl⟩ | ⟨i, rfl⟩) | hx)
  · exact (h1 i).trans (tor_e hH hF hδ0 u i).symm
  · exact (h2 i).trans (tor_f hH hF hδ0 u i).symm
  · exact (h3 x hx).trans (tor_w hH hF u hx).symm
end GlobalTheory.CompanionTheory.FrameTorus
