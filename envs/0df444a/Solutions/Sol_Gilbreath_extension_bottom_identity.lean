-- Prove2me | solution 1 for Gilbreath.extension_bottom_identity
-- status  : ACCEPTED   (prove)
-- author  : @EvanLLL
-- created : 2026-09-26T00:15:10.228804+00:00
-- url     : https://prove2.me/submissions/d0a50156-93e6-4554-9c50-ed0bbf37e55d

import Definitions.Def_gilbreath_finite_extension

set_option autoImplicit false
open Gilbreath

theorem solution (a : ℕ → ℕ) (n : ℕ) :
    extensionFold (extensionBoundary a n) (a n) = iterAbsDiff a n 0 := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
      change extensionFold (extensionBoundary (absDiff a) n)
        (absDiff a n) = iterAbsDiff a (n + 1) 0
      rw [ih, iterAbsDiff_succ']

#print axioms solution
