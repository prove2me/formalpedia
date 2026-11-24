-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FrameTorus.tor_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:36:05.411862+00:00
-- url     : https://prove2.me/submissions/d25d1c05-dc78-424f-829d-6b9d41a7e5d1

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TorusStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FrameTorus_span_gens
import Theorems.Thm_GlobalTheory_CompanionTheory_FrameTorus_pair_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_FrameTorus_tor_e
import Theorems.Thm_GlobalTheory_CompanionTheory_FrameTorus_tor_f
import Theorems.Thm_GlobalTheory_CompanionTheory_FrameTorus_tor_w
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
variable {s : L →+* L} {h : V → V → L} {δ : L} {l : ℕ} {e f : Fin l → V} {W : Submodule L V}
namespace GlobalTheory.CompanionTheory.FrameTorus
theorem _root_.solution (hH : IsHerm s h) (hF : IsFrame h δ e f W) (hδ : δ ≠ 0) (u : Fin l → L)
    (hu : ∀ i, u i ≠ 0) :
    (tor hH δ e f u).comp (tor hH δ e f fun i => (u i)⁻¹) = LinearMap.id := by
  refine LinearMap.ext_on (span_gens hF) ?_
  rintro x ((⟨i, rfl⟩ | ⟨i, rfl⟩) | hx)
  · simp [tor_e hH hF hδ, hu i]
  · have : s (u i) ≠ 0 := (map_ne_zero s).2 (hu i)
    simp [tor_e hH hF hδ, tor_f hH hF hδ, this]
  · simp [tor_w hH hF _ hx]
end GlobalTheory.CompanionTheory.FrameTorus
