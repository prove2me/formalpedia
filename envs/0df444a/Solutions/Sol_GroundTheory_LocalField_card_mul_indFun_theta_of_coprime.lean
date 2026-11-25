-- Prove2me | solution 1 for GroundTheory.LocalField.card_mul_indFun_theta_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:29:10.966499+00:00
-- url     : https://prove2.me/submissions/37dc4b3e-5a9d-484e-bbe2-569d8c46269b

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionLocal
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionPrime
import Theorems.Thm_GroundTheory_LocalField_card_mul_indFun_theta
import Theorems.Thm_GroundTheory_LocalField_mem_sylowCent_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
open scoped Classical
universe u
variable {G : Type u} [Group G]
variable [Fintype G] (p : ℕ) [hp : Fact p.Prime] (x : G)
variable {p x}
namespace GroundTheory.LocalField
theorem _root_.solution (hx : (orderOf x).Coprime p) {g : G}
    (hg : (orderOf g).Coprime p) :
    (Nat.card (sylowCent p x) : ℂ) * indFun (elemSub p x).subtype (theta p x) g =
      ∑ t : G, if t⁻¹ * g * t = x then 1 else 0 := by
  rw [card_mul_indFun_theta]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  have ht : (orderOf (t⁻¹ * g * t)).Coprime p := by
    have : t⁻¹ * g * t = (MulAut.conj t⁻¹) g := by simp
    rw [this, MulEquiv.orderOf_eq]
    exact hg
  by_cases h : t⁻¹ * g * t = x
  · rw [if_pos h, if_pos ((mem_sylowCent_iff hx ht).mpr h)]
  · rw [if_neg h, if_neg fun h' ↦ h ((mem_sylowCent_iff hx ht).mp h')]
end GroundTheory.LocalField
