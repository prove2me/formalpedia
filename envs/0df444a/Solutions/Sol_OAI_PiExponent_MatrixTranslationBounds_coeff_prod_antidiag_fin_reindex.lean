-- Prove2me | solution 1 for OAI.PiExponent.MatrixTranslationBounds.coeff_prod_antidiag_fin_reindex
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T17:40:46.954569+00:00
-- url     : https://prove2.me/submissions/b9d39a19-eeb6-4188-9d31-5d8f5ca20253

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.PowerSeries.Log
import Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_coeff_prod_antidiag_fin_reindex_weighted

open scoped BigOperators

theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → PowerSeries ℂ) (k : ℕ) :
    (∑ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) k,
      ∏ i, PowerSeries.coeff (l i) (g i)) =
    ∑ f : ι → Fin (k + 1),
      if (∑ i, (f i).val) = k then
        ∏ i, PowerSeries.coeff (f i).val (g i)
      else 0 := by
  simpa using
    OAI.PiExponent.MatrixTranslationBounds.coeff_prod_antidiag_fin_reindex_weighted
      (fun i n => PowerSeries.coeff n (g i)) k