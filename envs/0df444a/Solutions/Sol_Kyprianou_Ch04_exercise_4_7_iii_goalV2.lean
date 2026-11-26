-- Prove2me | solution 1 for Kyprianou.Ch04.exercise_4_7_iii_goalV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T08:21:27.595264+00:00
-- url     : https://prove2.me/submissions/76055668-d48f-407c-8412-2541cabeb99d

import Definitions.Def_Kyprianou_Ch04_Exercise4_7Certification
import Theorems.Thm_Kyprianou_Ch04_kw47_compactSup_integrable
import Theorems.Thm_Kyprianou_Ch04_kw47_trueMartingale_productGrid
set_option autoImplicit false
open Kyprianou.Ch04

theorem solution : certificate_ex4_7_iii := by
  intro Omega inst P F L alpha hAlpha
  exact ⟨kw47_compactSup_integrable P F L alpha hAlpha,
    kw47_trueMartingale_productGrid P F L alpha hAlpha⟩
