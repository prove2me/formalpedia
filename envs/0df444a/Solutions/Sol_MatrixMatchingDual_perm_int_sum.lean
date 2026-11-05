-- Prove2me | solution 1 for MatrixMatchingDual.perm_int_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.80903+00:00
-- url     : https://prove2.me/submissions/16dd23f0-f972-4e1e-a1f3-90ae6b2ed18a

import Std
import Definitions.Def_MatchingDual

set_option autoImplicit true
open MatrixMatchingDual
namespace MatrixMatchingDual
theorem _root_.solution {xs ys : List Int} (h : List.Perm xs ys) : xs.sum = ys.sum := by
  induction h with
  | nil => rfl
  | cons a h ih => simp only [List.sum_cons,ih]
  | swap a b xs => simp only [List.sum_cons]; omega
  | trans hxy hyz ihxy ihyz => exact ihxy.trans ihyz
end MatrixMatchingDual
