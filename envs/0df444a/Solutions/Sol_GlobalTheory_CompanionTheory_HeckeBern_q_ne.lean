-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeBern.q_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:56:51.913628+00:00
-- url     : https://prove2.me/submissions/ec0f079f-3905-4870-89b5-36f15fe2419f

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeOperatorsSpanAndFaithful
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeAlgebraStatement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.Fl
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeBern
variable {G : Type} [Group G] {K : Subgroup G}
variable (T : G → Hk K) (hp : IsHeckePair K)
namespace GlobalTheory.CompanionTheory.HeckeBern
theorem _root_.solution (g : G) : q hp g ≠ 0 := by
  rw [q, Nat.cast_ne_zero, Finset.card_ne_zero]
  exact ⟨(g : G ⧸ K), (hp g).mem_toFinset.2 (MulAction.mem_orbit_self _)⟩
end GlobalTheory.CompanionTheory.HeckeBern
