-- Prove2me | solution 1 for HerbstGeneral.ratio_le_integral
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-23T03:25:33.806266+00:00
-- url     : https://prove2.me/submissions/e9f3131e-ca95-4c68-9eca-457f2b7ea628

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
open Set Filter Topology intervalIntegral MeasureTheory

theorem solution
    (ρ ρ' g : ℝ → ℝ) (lam : ℝ)
    (hlam : 0 ≤ lam)
    (hρ_cont : ContinuousOn ρ (Set.Icc 0 lam))
    (hg_cont : Continuous g)
    (hρ_deriv : ∀ x ∈ Set.Ico (0 : ℝ) lam, HasDerivWithinAt ρ (ρ' x) (Set.Ici x) x)
    (hbound : ∀ x ∈ Set.Ico (0 : ℝ) lam, ρ' x ≤ g x) :
    ρ lam ≤ ρ 0 + ∫ x in (0:ℝ)..lam, g x := by
  set H : ℝ → ℝ := fun x => ρ 0 + ∫ t in (0:ℝ)..x, g t with hH
  have hH_cont : ContinuousOn H (Icc 0 lam) := by
    apply ContinuousOn.add continuousOn_const
    apply Continuous.continuousOn
    exact intervalIntegral.continuous_primitive (fun a b => hg_cont.intervalIntegrable a b) 0
  have hH_deriv : ∀ x ∈ Ico (0:ℝ) lam, HasDerivWithinAt H (g x) (Ici x) x := by
    intro x _
    have hbase : HasDerivWithinAt (fun u => ∫ t in (0:ℝ)..u, g t) (g x) (Ici x) x :=
      integral_hasDerivWithinAt_right (hg_cont.intervalIntegrable 0 x)
        (hg_cont.stronglyMeasurableAtFilter volume _) hg_cont.continuousWithinAt
    exact (hbase.const_add (ρ 0))
  have key : ∀ ⦃x⦄, x ∈ Icc (0:ℝ) lam → ρ x ≤ H x := by
    refine image_le_of_deriv_right_le_deriv_boundary hρ_cont hρ_deriv ?_ hH_cont hH_deriv hbound
    simp [hH]
  have := key (right_mem_Icc.mpr hlam)
  simpa [hH] using this
