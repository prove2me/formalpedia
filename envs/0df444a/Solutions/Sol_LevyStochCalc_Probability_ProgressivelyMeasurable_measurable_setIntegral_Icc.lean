-- Prove2me | solution 1 for LevyStochCalc.Probability.ProgressivelyMeasurable.measurable_setIntegral_Icc
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T06:31:40.236286+00:00
-- url     : https://prove2.me/submissions/991ebe9c-3882-4cf2-b557-172d12079584

import Definitions.Def_LevyStochCalc_Probability_Progressive_F002
import Mathlib.MeasureTheory.Function.Floor

open MeasureTheory Filter Topology

namespace LevyStochCalc.Probability

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

theorem _root_.solution
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {H : Ω → ℝ → ℝ}
    (h : ProgressivelyMeasurable ℱ H) (t : ℝ) :
    Measurable[ℱ t] fun ω => ∫ s in Set.Icc (0 : ℝ) t, H ω s ∂volume := by
  have key : StronglyMeasurable[ℱ t] (fun ω => ∫ s, (Set.Iic t).indicator (H ω) s
      ∂(volume.restrict (Set.Icc (0 : ℝ) t))) := by
    letI : MeasurableSpace Ω := ℱ t
    exact (h t).integral_prod_right'
  have e : (fun ω => ∫ s in Set.Icc (0 : ℝ) t, H ω s ∂volume)
      = fun ω => ∫ s, (Set.Iic t).indicator (H ω) s ∂(volume.restrict (Set.Icc (0 : ℝ) t)) := by
    funext ω
    refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
    exact (Set.indicator_of_mem (Set.Icc_subset_Iic_self hs) _).symm
  rw [e]
  exact key.measurable

end LevyStochCalc.Probability
