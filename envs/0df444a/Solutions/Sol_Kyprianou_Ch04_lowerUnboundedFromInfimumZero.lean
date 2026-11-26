-- Prove2me | solution 1 for Kyprianou.Ch04.lowerUnboundedFromInfimumZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:47:44.715165+00:00
-- url     : https://prove2.me/submissions/d405117e-2823-4802-9e87-49a1d1c8c1f0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_runningInfimumExpRewardProperties
import Theorems.Thm_Kyprianou_Ch04_unboundedBelowOfVanishingLaplace
import Theorems.Thm_Kyprianou_Ch04_boundedRewardThresholdMass
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Vanishing infimum transforms force the original paths to be unbounded below. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (beta : ℝ) (hb : 0 < beta)
    (hlim : Tendsto (fun t : NNReal => ∫ w, Real.exp (beta * sInf ((fun s : NNReal => L.X s w) '' Iic t)) ∂P)
      atTop (nhds 0)) :
    P {w | BddBelow (range (fun t : NNReal => L.X t w))} = 0 := by
  let : IsProbabilityMeasure P := L.isProbability
  let g : NNReal × Ω → ℝ := fun z => Real.exp (beta * sInf ((fun s : NNReal => L.X s z.2) '' Iic z.1))
  obtain ⟨hg,hg0,hg1,hga⟩ := Kyprianou.Ch04.runningInfimumExpRewardProperties P F L beta hb
  let a : ℕ → ℝ := fun n => ∫ w, g ((n : NNReal),w) ∂P
  have hcast : Tendsto (fun n : ℕ => (n : NNReal)) atTop atTop := tendsto_natCast_atTop_atTop
  have ha : Tendsto a atTop (nhds 0) := hlim.comp hcast
  apply Kyprianou.Ch04.unboundedBelowOfVanishingLaplace P L.X a beta ha
  intro K n
  let E : Set Ω := {w | ∀ t : NNReal, -(K : ℝ) ≤ L.X t w}
  let c := Real.exp (-beta * (K : ℝ))
  apply Kyprianou.Ch04.boundedRewardThresholdMass P (fun w => g ((n : NNReal),w))
    (hg.comp (measurable_const.prodMk measurable_id)) (fun w => hg0 _) (fun w => hg1 _)
    E c (Real.exp_pos _).le
  intro w hw
  change c ≤ Real.exp (beta * sInf ((fun s : NNReal => L.X s w) '' Iic (n : NNReal)))
  apply Real.exp_le_exp.mpr
  have hn : (((fun s : NNReal => L.X s w) '' Iic (n : NNReal))).Nonempty := ⟨L.X 0 w,0,by simp,rfl⟩
  have hI : -(K : ℝ) ≤ sInf ((fun s : NNReal => L.X s w) '' Iic (n : NNReal)) := by
    apply le_csInf hn
    rintro y ⟨t,ht,rfl⟩
    exact hw t
  rw [neg_mul]
  simpa only [neg_mul, mul_neg] using mul_le_mul_of_nonneg_left hI hb.le
