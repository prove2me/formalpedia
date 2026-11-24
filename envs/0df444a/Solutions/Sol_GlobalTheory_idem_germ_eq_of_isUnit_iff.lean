-- Prove2me | solution 1 for GlobalTheory.idem_germ_eq_of_isUnit_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:00:12.224926+00:00
-- url     : https://prove2.me/submissions/18b3c909-3598-43d6-9a11-f7b5be1a7e36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdempotentEqOfBasicOpenEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R : Type*} [CommRing R] [IsLocalRing R] {a b : R}
    (ha : a * a = a) (hb : b * b = b) (h : IsUnit a ↔ IsUnit b) : a = b := by
  have key : ∀ c : R, c * c = c → (IsUnit c → c = 1) ∧ (¬ IsUnit c → c = 0) := by
    intro c hc
    refine ⟨fun hu => ?_, fun hn => ?_⟩
    · obtain ⟨u, rfl⟩ := hu
      have : (u : R) * u = u * 1 := by rw [mul_one]; exact hc
      exact (Units.mul_right_inj u).mp this
    · rcases IsLocalRing.isUnit_or_isUnit_one_sub_self c with h1 | h1
      · exact absurd h1 hn
      · have : (1 - c) * c = 0 := by rw [sub_mul, one_mul, hc, sub_self]
        obtain ⟨u, hu⟩ := h1
        rw [← hu] at this
        simpa using this
  by_cases hau : IsUnit a
  · rw [(key a ha).1 hau, (key b hb).1 (h.mp hau)]
  · rw [(key a ha).2 hau, (key b hb).2 (fun hbu => hau (h.mpr hbu))]
end GlobalTheory
