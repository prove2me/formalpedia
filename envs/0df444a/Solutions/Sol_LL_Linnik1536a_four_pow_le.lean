-- Prove2me | solution 1 for LL_Linnik1536a.four_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:47:16.193257+00:00
-- url     : https://prove2.me/submissions/4c5b1181-5dad-40b4-8655-384fa4da4c98

import Mathlib
import Definitions.Def_LL_Linnik1536a_Gpow
import Definitions.Def_LL_Linnik1536a_Spow
import Definitions.Def_LL_Linnik1536a_EL
import Definitions.Def_LL_Linnik1536a_devSet
open Real MeasureTheory Finset

theorem solution (j : ℕ) : (4 : ℝ) ^ j ≤ (2 * j + 1) * Nat.centralBinom j := by
  exact_mod_cast Nat.four_pow_le_two_mul_add_one_mul_central_binom j
