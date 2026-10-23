-- Prove2me | solution 1 for LeanTT2.algo_not_transitive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:27:12.505684+00:00
-- url     : https://prove2.me/submissions/f8caeb8e-f9b2-48a5-aea7-189401a43559

import Mathlib
import Definitions.Def_LeanTT2_frag
import Definitions.Def_LeanTT2_spec
import Definitions.Def_LeanTT2_counter

universe u

open LeanTT2

theorem solution (F : Frag.{u}) (C : Counter F) :
    ∃ a b c, F.alg C.Γ a b ∧ F.alg C.Γ b c ∧ ¬ F.alg C.Γ a c :=
  ⟨C.x, C.y, C.z, C.halg1, C.halg2, C.halg3⟩
