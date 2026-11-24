-- Prove2me | solution 1 for GlobalTheory.RatCoordsAdjoin.exists_rat_add_mul_of_mem_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:51:42.441944+00:00
-- url     : https://prove2.me/submissions/62527bbc-3e8b-4e6d-95a7-e986fb6ddaaf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsRatAddMulOfMemAdjoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RatCoordsAdjoin
namespace GlobalTheory.RatCoordsAdjoin
theorem _root_.solution {E : Type} [Field E] [NumberField E] (d : ℕ) (s : E)
    (hs : s ^ 2 = -(d : E)) {x : E} (hx : x ∈ IntermediateField.adjoin ℚ ({s} : Set E)) :
    ∃ a b : ℚ, x = (a : E) + (b : E) * s := by
  have halg : IsAlgebraic ℚ s := Algebra.IsAlgebraic.isAlgebraic s
  have hx' : x ∈ Algebra.adjoin ℚ ({s} : Set E) := by
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (F := ℚ) (S := ({s} : Set E))
      (by intro y hy; rw [Set.mem_singleton_iff.mp hy]; exact halg)]
    exact hx
  clear hx
  induction hx' using Algebra.adjoin_induction with
  | mem y hy => exact ⟨0, 1, by rw [Set.mem_singleton_iff.mp hy]; simp⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨c, e, rfl⟩ := hz
    exact ⟨a + c, b + e, by push_cast; ring⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨c, e, rfl⟩ := hz
    exact ⟨a * c - b * e * d, a * e + b * c, by
      push_cast; linear_combination ((b : E) * (e : E)) * hs⟩
end GlobalTheory.RatCoordsAdjoin
