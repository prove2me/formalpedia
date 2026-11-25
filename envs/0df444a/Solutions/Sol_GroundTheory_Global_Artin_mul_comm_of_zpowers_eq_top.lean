-- Prove2me | solution 1 for GroundTheory.Global.Artin.mul_comm_of_zpowers_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:08:17.132502+00:00
-- url     : https://prove2.me/submissions/fb0f3ad9-3c38-403d-bd9a-816cd235e2d6

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_Mackey
import Definitions.Def_GroundTheory_GlobalFields_Artin_MackeyFrobenius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped Pointwise
open GroundTheory GroundTheory.Global GroundTheory.Global.Artin
open GroundTheory.LocalField
variable {Γ : Type*} [Group Γ] {N : Subgroup Γ} [N.Normal] {g : Γ}
namespace GroundTheory.Global.Artin
theorem _root_.solution {Q : Type*} [Group Q] {c : Q} (h : Subgroup.zpowers c = ⊤)
    (a b : Q) : a * b = b * a := by
  have ha : a ∈ Subgroup.zpowers c := by rw [h]; exact Subgroup.mem_top a
  have hb : b ∈ Subgroup.zpowers c := by rw [h]; exact Subgroup.mem_top b
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  exact zpow_mul_comm c j k
end GroundTheory.Global.Artin
