-- Prove2me | solution 1 for Kyprianou.Ch04.infimumLimitSupport
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:50:19.489099+00:00
-- url     : https://prove2.me/submissions/07d4d9d3-c7fd-460e-a427-2da78e88d48d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_path_bddBelow_finite_horizon
import Theorems.Thm_Kyprianou_Ch04_runningInfimumExpRewardProperties
import Theorems.Thm_Kyprianou_Ch04_lowerBoundIffPositiveInfimumReward
import Theorems.Thm_Kyprianou_Ch04_boundedRewardLimitSupport
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Long-horizon infimum rewards are supported on the lower-bounded path event. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (beta : ℝ) (hb : 0 < beta) :
    let B : Set Ω := {w | BddBelow (range (fun t : NNReal => L.X t w))}
    let f : NNReal → ℝ := fun t => ∫ w, Real.exp (beta * sInf ((fun s : NNReal => L.X s w) '' Iic t)) ∂P
    MeasurableSet B ∧
      (∀ ell : ℝ, Tendsto f atTop (nhds ell) → ell ≤ (P B).toReal) ∧
      (P B = 0 → Tendsto f atTop (nhds 0)) := by
  intro B f
  let : IsProbabilityMeasure P := L.isProbability
  let g : NNReal × Ω → ℝ := fun z => Real.exp (beta * sInf ((fun s : NNReal => L.X s z.2) '' Iic z.1))
  obtain ⟨hg,hg0,hg1,hga⟩ := Kyprianou.Ch04.runningInfimumExpRewardProperties P F L beta hb
  apply Kyprianou.Ch04.boundedRewardLimitSupport P g hg hg0 hg1 hga B
  intro w
  apply Kyprianou.Ch04.lowerBoundIffPositiveInfimumReward (fun t => L.X t w) beta hb
  intro t
  convert levy_path_bddBelow_finite_horizon L t w using 1
  ext y
  constructor <;> rintro ⟨s,hs,he⟩ <;> exact ⟨s,hs,he.symm⟩
