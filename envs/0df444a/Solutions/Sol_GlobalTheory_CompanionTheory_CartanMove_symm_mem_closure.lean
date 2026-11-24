-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartanMove.symm_mem_closure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:21:41.099114+00:00
-- url     : https://prove2.me/submissions/8d924e14-1e13-4d22-9a76-3f359c91ada0

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MovingStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_CartanMove_closure_symm_eq

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
theorem _root_.solution (e : G ≃* G') {l : ℕ} (t' : Fin l → G') {s : G'}
    (hs : s ∈ Submonoid.closure (Set.range t')) :
    e.symm s ∈ Submonoid.closure (Set.range fun j => e.symm (t' j)) := by
  rw [closure_symm_eq]
  exact ⟨s, hs, rfl⟩
end GlobalTheory.CompanionTheory.CartanMove
