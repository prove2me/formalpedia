-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.eventual_translation_remainder_lt_eighth
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T22:50:34.775651+00:00
-- url     : https://prove2.me/submissions/c6674e5d-d769-4f75-92fc-e0098ad2be50

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_translationTermCount_log_div_tendsto_zero

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem solution
    {nu : ℝ} (d : FixedData nu) :
    ∀ᶠ H : ℝ in atTop,
      Real.log (translationTermCount d.m d.v0 H : ℝ) / H < 1 / 8 := by
  have hlim :=
    OAI.PiExponent.DeterminantContradiction.translationTermCount_log_div_tendsto_zero
      d.m (v := (d.v0 : ℝ)) d.v0_pos
  exact hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))