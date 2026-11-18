-- Prove2me | solution 1 for Kyprianou.Ch01.riskPositiveTailPushforward
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T00:49:25.4282+00:00
-- url     : https://prove2.me/submissions/06faa7ef-0bf9-4a61-a901-2c39fd2a1342

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution (beta : ℝ) (F : Measure ℝ) [IsProbabilityMeasure F] :
    let Ebeta : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun e : ℝ => ENNReal.ofReal (beta * Real.exp (-beta * e)))
    let mu : Measure ℝ := (Ebeta.prod F).map
      (fun pair : ℝ × ℝ => pair.1 - pair.2)
    ∀ z : ℝ, mu (Set.Ioi z) =
      ∫⁻ u : ℝ, Ebeta (Set.Ioi (z + u)) ∂F := by
  intro Ebeta mu z
  have hm : Measurable (fun p : ℝ × ℝ => p.1 - p.2) :=
    measurable_fst.sub measurable_snd
  have hs : MeasurableSet ((fun p : ℝ × ℝ => p.1 - p.2) ⁻¹'
    Set.Ioi z) := hm measurableSet_Ioi
  have hsec (u : ℝ) :
      Ebeta ((fun e : ℝ => (e, u)) ⁻¹'
        ((fun p : ℝ × ℝ => p.1 - p.2) ⁻¹' Set.Ioi z)) =
      Ebeta (Set.Ioi (z + u)) := by
    congr 1
    ext e
    simp only [Set.mem_preimage, Set.mem_Ioi]
    constructor <;> intro h <;> linarith
  change ((Ebeta.prod F).map (fun p : ℝ × ℝ => p.1 - p.2)) (Set.Ioi z) = _
  rw [Measure.map_apply hm measurableSet_Ioi, Measure.prod_apply_symm hs]
  exact lintegral_congr (fun u => hsec u)
