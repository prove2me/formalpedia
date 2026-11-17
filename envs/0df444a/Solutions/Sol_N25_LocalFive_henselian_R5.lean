-- Prove2me | solution 1 for N25.LocalFive.henselian_R5
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:26:22.821204+00:00
-- url     : https://prove2.me/submissions/f52c631e-920a-4b12-9fa3-d14299167d02

import Mathlib
import Definitions.Def_N25_LocalFiveArithmetic
import Theorems.Thm_HenselianLocalRing_of_isAdicComplete_maximalIdeal

noncomputable section

local instance instL_N25_LocalFive_henselian_R5_bfd51b_sa5b823 : Fact (Nat.Prime 5) := ⟨by decide⟩

namespace N25.LocalFive

/-- The ring of 5-adic integers is Henselian by adic completeness. -/
theorem _root_.solution : HenselianLocalRing R5 :=
  HenselianLocalRing.of_isAdicComplete_maximalIdeal R5

end N25.LocalFive
