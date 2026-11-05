-- Prove2me | solution 1 for MatrixMatchingDual.unused_sum_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.80903+00:00
-- url     : https://prove2.me/submissions/8b6d1dd3-78a1-44e3-98a6-fce43a751b0d

import Std
import Definitions.Def_MatchingDual

set_option autoImplicit true
open MatrixMatchingDual
namespace MatrixMatchingDual
theorem _root_.solution (unused : List Int) (h : ∀ p ∈ unused, p = 0) :
    unused.sum = 0 := by
  induction unused with
  | nil => rfl
  | cons p ps ih =>
    have hp := h p (by simp)
    have hrest : ∀ q ∈ ps, q = 0 := by intro q hq; exact h q (by simp [hq])
    have hs := ih hrest
    simp only [List.sum_cons,hp,hs]
    omega
end MatrixMatchingDual
