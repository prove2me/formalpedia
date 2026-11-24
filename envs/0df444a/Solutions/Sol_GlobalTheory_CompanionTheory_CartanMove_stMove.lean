-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartanMove.stMove
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:55:19.149163+00:00
-- url     : https://prove2.me/submissions/3e580d5f-10e0-4354-bb22-014c8c407a83

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MovingStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_CartanMove_isCartan_comap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.Fl
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartanMove
variable {G G' : Type} [Group G] [Group G']
namespace GlobalTheory.CompanionTheory.CartanMove
theorem _root_.solution : StMove := by
  intro G G' _ _ _ _ e h U hU
  have hopen : IsOpen ((U.map e.toMulEquiv.toMonoidHom : Subgroup G') : Set G') := by
    have : ((U.map e.toMulEquiv.toMonoidHom : Subgroup G') : Set G') = e.toHomeomorph '' (U : Set G) := rfl
    rw [this]
    exact e.toHomeomorph.isOpenMap _ hU
  obtain ⟨K', hK'U, hoK', hcK', d, l, hC⟩ := h _ hopen
  refine ⟨K'.comap e.toMulEquiv.toMonoidHom, ?_, ?_, ?_, d, l, isCartan_comap _ hC⟩
  · intro x hx
    obtain ⟨u, hu, hux⟩ := hK'U hx
    have : u = x := e.toMulEquiv.injective hux
    exact this ▸ hu
  · exact hoK'.preimage e.toHomeomorph.continuous
  · exact e.toHomeomorph.isCompact_preimage.2 hcK'
end GlobalTheory.CompanionTheory.CartanMove
