-- Prove2me | solution 1 for GlobalTheory.isUnit_of_isUnit_map_of_ker_le_jacobson
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:11:08.211226+00:00
-- url     : https://prove2.me/submissions/c168ae8b-b9f1-4dad-abc0-45d0ec119792

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial IsLocalRing
open scoped TensorProduct
variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]
namespace GlobalTheory
theorem _root_.solution (π : B →+* C) (hπ : Function.Surjective π)
    (hj : RingHom.ker π ≤ Ideal.jacobson ⊥) {b : B} (hb : IsUnit (π b)) : IsUnit b := by
  obtain ⟨c, hc⟩ := hb.exists_right_inv
  obtain ⟨a, rfl⟩ := hπ c
  have h : b * a - 1 ∈ RingHom.ker π := by simp [RingHom.mem_ker, hc]
  have := Ideal.mem_jacobson_bot.mp (hj h) 1
  rw [mul_one, sub_add_cancel] at this
  exact isUnit_of_mul_isUnit_left this
end GlobalTheory
