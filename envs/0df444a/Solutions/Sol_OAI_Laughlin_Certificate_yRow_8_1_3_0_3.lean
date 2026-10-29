-- Prove2me | solution 3 for OAI.Laughlin.Certificate.yRow_8_1_3_0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:07:08.654194+00:00
-- url     : https://prove2.me/submissions/f8e7f323-9b97-43ae-b975-6130e3d45cae

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : yRow 8 1 3 (rows[0]!) = (-11387494346113586295/8192 : ℚ) := by
  simp only [yRow, yEntry, V, U, Nat.choose_eq_fast_choose]
  decide +kernel
