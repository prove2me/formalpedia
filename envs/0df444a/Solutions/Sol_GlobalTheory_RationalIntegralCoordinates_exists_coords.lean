-- Prove2me | solution 1 for GlobalTheory.RationalIntegralCoordinates.exists_coords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:51:47.17194+00:00
-- url     : https://prove2.me/submissions/3cf83efd-50bd-49f5-ba2d-2d7d15ebbf07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IntOfPrimeMulSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RationalIntegralCoordinates
namespace GlobalTheory.RationalIntegralCoordinates
theorem _root_.solution {d : ℕ} (hd : 0 < d) {r : ℂ} (hr : r ^ 2 = -(d : ℂ)) {z : ℂ}
    (hzK : z ∈ IntermediateField.adjoin ℚ ({r} : Set ℂ)) :
    ∃ a b : ℚ, z = (a : ℂ) + (b : ℂ) * r := by
  have hint : IsIntegral ℚ r := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℚ), Polynomial.monic_X_pow_add_C _ two_ne_zero, ?_⟩
    simp [hr]
  rw [← IntermediateField.mem_toSubalgebra,
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic] at hzK
  induction hzK using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, by simp [hx]⟩
  | algebraMap q => exact ⟨q, 0, by simp [eq_ratCast]⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, e, rfl⟩ := hy
    exact ⟨a + c, b + e, by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, e, rfl⟩ := hy
    refine ⟨a * c - d * b * e, a * e + b * c, ?_⟩
    push_cast
    linear_combination (b : ℂ) * e * hr
end GlobalTheory.RationalIntegralCoordinates
