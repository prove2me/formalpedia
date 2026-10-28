-- Prove2me | solution 1 for LL_Linnik1536a.devSet_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T22:03:23.487767+00:00
-- url     : https://prove2.me/submissions/45300742-a95f-4555-bafa-8d1be86626ec

import Mathlib
import Definitions.Def_LL_Linnik1536a_Gpow
import Definitions.Def_LL_Linnik1536a_Spow
import Definitions.Def_LL_Linnik1536a_EL
import Definitions.Def_LL_Linnik1536a_devSet
import Theorems.Thm_LL_Linnik1536a_markov
import Theorems.Thm_LL_Linnik1536a_lemma4_GL
open Real MeasureTheory Finset

theorem solution (L : ℕ) (d : ℝ) {lam : ℝ} (hlam : 0 ≤ lam) :
    volume (LL_Linnik1536a.devSet L d) ≤
      ENNReal.ofReal (11 * (1 + lam * L) * Real.exp (-(lam * d * L)) * LL_Linnik1536a.EL L lam) := by
  refine (LL_Linnik1536a.markov (L := L) (d := d) hlam).trans (ENNReal.ofReal_le_ofReal ?_)
  have h := LL_Linnik1536a.lemma4_GL L hlam
  have he := (Real.exp_pos (-(lam * d * L))).le
  calc Real.exp (-(lam * d * L)) * ∫ x in (0 : ℝ)..1, Real.exp (lam * ‖LL_Linnik1536a.Gpow L x‖)
      ≤ Real.exp (-(lam * d * L)) * (11 * (1 + lam * L) * LL_Linnik1536a.EL L lam) :=
        mul_le_mul_of_nonneg_left h he
    _ = _ := by ring
