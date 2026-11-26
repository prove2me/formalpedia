-- Prove2me | solution 1 for O3.lpNorm_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:55:02.290379+00:00
-- url     : https://prove2.me/submissions/b66ff636-60e2-43c8-9b06-58037a1b4427

import Mathlib
import Definitions.Def_O3_Geometry
import Theorems.Thm_O3_lpNorm_zero
import Theorems.Thm_O3_lpNorm_pos_of_ne_zero
attribute [local simp] O3.lpNorm_zero

set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution {p : ℝ} (hp : 0 < p) {d : ℕ} {x : Point d} :
    lpNorm p x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    exact (lpNorm_pos_of_ne_zero hx).ne' h
  · rintro rfl
    exact lpNorm_zero hp
end O3
