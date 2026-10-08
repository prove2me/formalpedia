-- Prove2me | solution 1 for LLLFactor.Reduction.situation_initial_final
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T19:54:03.834269+00:00
-- url     : https://prove2.me/submissions/c91c2230-2072-4e26-b18c-ab3ce7770ba7

import Mathlib
import Definitions.Def_LLLFactor_Reduction_Algorithm

open LLLFactor.Reduction LLLFactor.RedBasis

theorem solution {n : ℕ} (b : Fin n → Vec n) :
    Situation b 2 ∧ (Situation b (n + 1) → IsReduced b) := by
  constructor
  · constructor
    · intro i j hji hi
      have := j.isLt
      omega
    · intro i hi hik hin
      omega
  · rintro ⟨hs, hl⟩
    constructor
    · intro i j hji
      exact hs i j hji (by omega)
    · intro i hi
      obtain ⟨h, hh⟩ := hl (i + 2) (by omega) (by omega) (by omega)
      simpa using hh

#print axioms solution
