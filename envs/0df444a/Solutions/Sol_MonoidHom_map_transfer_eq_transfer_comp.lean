-- Prove2me | solution 1 for MonoidHom.map_transfer_eq_transfer_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/273b535d-f30f-5ec7-83bf-e3daeb392817

import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.Abelianization.Defs
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MonoidHom_map_transfer_eq_transfer_comp

set_option autoImplicit false

theorem solution
    {G : Type*} [Group G] {H : Subgroup G} [H.FiniteIndex]
    {A B : Type*} [CommGroup A] [CommGroup B] (ϕ : ↥H →* A) (f : A →* B) (g : G) :
    f (MonoidHom.transfer ϕ g) = MonoidHom.transfer (f.comp ϕ) g := by
  classical
  rw [MonoidHom.transfer_def ϕ (default : H.LeftTransversal) g,
    MonoidHom.transfer_def (f.comp ϕ) (default : H.LeftTransversal) g]
  unfold Subgroup.leftTransversals.diff
  simp only [map_prod, MonoidHom.comp_apply]

end S_MonoidHom_map_transfer_eq_transfer_comp
end P2MW
export P2MW.S_MonoidHom_map_transfer_eq_transfer_comp (solution)
