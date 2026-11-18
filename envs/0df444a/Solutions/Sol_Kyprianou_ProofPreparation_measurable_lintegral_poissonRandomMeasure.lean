-- Prove2me | solution 1 for Kyprianou.ProofPreparation.measurable_lintegral_poissonRandomMeasure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T13:18:27.66221+00:00
-- url     : https://prove2.me/submissions/6055a5ec-b227-46f4-92bc-ee00830a77ff

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

/-- Nonnegative Poisson integrals are measurable as monotone limits of simple integrals. -/
theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    {g : E → ENNReal} (hg : Measurable g) :
    Measurable (fun ω => ∫⁻ x, g x ∂
      (ProbabilityTheory.poissonRandomMeasure K Y ω)) := by
  have hs : ∀ s : SimpleFunc E ENNReal,
      Measurable (fun ω => s.lintegral (poissonRandomMeasure K Y ω)) := by
    intro s
    simp only [SimpleFunc.lintegral]
    exact Finset.measurable_sum _ fun x _ => measurable_const.mul
      (measurable_poissonRandomMeasure_apply hd.measurable_count
        hd.measurable_point (s.measurableSet_fiber x))
  simp_rw [lintegral_eq_iSup_eapprox_lintegral hg]
  exact Measurable.iSup fun n => hs (SimpleFunc.eapprox g n)
