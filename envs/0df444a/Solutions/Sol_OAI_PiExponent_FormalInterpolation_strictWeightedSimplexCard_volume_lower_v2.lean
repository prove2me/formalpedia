-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.strictWeightedSimplexCard_volume_lower_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T08:54:01.195728+00:00
-- url     : https://prove2.me/submissions/7460bfa3-a2b6-4bc0-9944-953adc0828af

import Definitions.Def_OAI_PiExponent_StrictWeightedSimplex
import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_strictWeightedSimplexCard_volume_lower

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution
    {ι : Type*} [Fintype ι] (v : ι → Rat)
    (hv : ∀ i, 0 < (v i : Real)) (T : Real) (hT : 0 < T) :
    Finite (strictWeightedSimplex v T) ∧
      T ^ Fintype.card ι ≤
        ((Fintype.card ι).factorial : Real) * (∏ i, (v i : Real)) *
          (strictWeightedSimplexCard v T : Real) :=
  OAI.PiExponent.FormalInterpolation.strictWeightedSimplexCard_volume_lower v hv T hT
