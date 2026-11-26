-- Prove2me | solution 1 for Kyprianou.Ch04.nonSingularInfimumTransform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:50:50.796015+00:00
-- url     : https://prove2.me/submissions/9188005d-0687-455e-a9bf-81ae3d0bf48d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_runningInfimumExpRewardProperties
import Theorems.Thm_Kyprianou_Ch04_positiveDiscountSequenceAndClockError
import Theorems.Thm_Kyprianou_Ch04_boundedRewardClockLimitData
import Theorems.Thm_Kyprianou_Ch04_infimumClockWhLimit
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Corollary 4.9 for every nonsingular Laplace argument, on the original process. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (hNotNegativeSubordinator : ¬ (∀ᵐ w : Ω ∂P, Antitone (fun t : NNReal => L.X t w)))
    (beta : ℝ) (hb : 0 < beta) (hpsi : L.ψ beta ≠ 0) :
    Tendsto (fun t : NNReal => ∫ w, Real.exp (beta * sInf ((fun s : NNReal => L.X s w) '' Iic t)) ∂P)
      atTop (nhds (max 0 (sInf ((fun theta : ℝ => L.ψ theta / theta) '' Ioi 0)) * beta / L.ψ beta)) := by
  let : IsProbabilityMeasure P := L.isProbability
  let g : NNReal × Ω → ℝ := fun z => Real.exp (beta * sInf ((fun s : NNReal => L.X s z.2) '' Iic z.1))
  let q : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  obtain ⟨hg,hg0,hg1,hga⟩ := Kyprianou.Ch04.runningInfimumExpRewardProperties P F L beta hb
  obtain ⟨hq,hq0,herr⟩ := Kyprianou.Ch04.positiveDiscountSequenceAndClockError
  obtain ⟨ell,hlim,hclock⟩ := Kyprianou.Ch04.boundedRewardClockLimitData P g hg hg0 hg1 hga q hq herr
  have hw := Kyprianou.Ch04.infimumClockWhLimit P F L hNotNegativeSubordinator q hq hq0 beta hb hpsi
  have he := tendsto_nhds_unique hclock hw
  rwa [he] at hlim
