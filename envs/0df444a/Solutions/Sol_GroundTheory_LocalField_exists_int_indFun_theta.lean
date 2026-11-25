-- Prove2me | solution 1 for GroundTheory.LocalField.exists_int_indFun_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:01:05.058206+00:00
-- url     : https://prove2.me/submissions/7bd02165-484c-4625-9236-ef7b1c53e66e

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionLocal
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionPrime
import Theorems.Thm_GroundTheory_LocalField_card_mul_indFun_theta
import Theorems.Thm_GroundTheory_LocalField_indFun_theta_mem_spanA
import Theorems.Thm_GroundTheory_LocalField_apply_mem_adjoin_of_mem_spanA
import Theorems.Thm_GroundTheory_LocalField_exists_int_of_mul_eq_int


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
variable {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Nat.card G))
  (hmono : ∀ K : Subgroup G, IsElementaryAt p K → ∀ χ : K → ℂ, IsIrrCharacter χ →
    ∃ (L : Subgroup K) (μ : L →* ℂˣ), χ = indLin L μ)
omit hp
include hζ hmono
namespace GroundTheory.LocalField
theorem _root_.solution (hx : (orderOf x).Coprime p) (g : G) :
    ∃ k : ℤ, indFun (elemSub p x).subtype (theta p x) g = k := by
  have hA := apply_mem_adjoin_of_mem_spanA hζ (indFun_theta_mem_spanA hζ hmono hx) g
  have hcount := card_mul_indFun_theta (p := p) (x := x) g
  obtain ⟨z, hz, -⟩ := exists_int_of_mul_eq_int (hζ.isIntegral Nat.card_pos) hA
    (d := Nat.card (sylowCent p x)) (k := ∑ t : G, if x⁻¹ * (t⁻¹ * g * t) ∈ sylowCent p x then 1 else 0)
    (Int.natCast_ne_zero.mpr Nat.card_pos.ne') (by push_cast; exact hcount)
  exact ⟨z, hz⟩
end GroundTheory.LocalField
