-- Prove2me | solution 1 for O3.lpPower_pos_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:50:35.22068+00:00
-- url     : https://prove2.me/submissions/fa922a7e-a9d2-426a-985a-6b7abbd27349

import Mathlib
import Definitions.Def_O3_Geometry

set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution {p : ℝ} {d : ℕ} {x : Point d}
    (hx : x ≠ 0) : 0 < lpPower p x := by
  classical
  have hex : ∃ i, x i ≠ 0 := by
    by_contra h
    apply hx
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hex
  have hterm : 0 < |x i| ^ p := Real.rpow_pos_of_pos (abs_pos.mpr hi) p
  exact hterm.trans_le (Finset.single_le_sum
    (fun j _ ↦ Real.rpow_nonneg (abs_nonneg (x j)) p) (Finset.mem_univ i))
end O3
