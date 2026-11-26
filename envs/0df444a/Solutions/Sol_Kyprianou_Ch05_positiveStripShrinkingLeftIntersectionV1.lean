-- Prove2me | solution 1 for Kyprianou.Ch05.positiveStripShrinkingLeftIntersectionV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:26:59.665415+00:00
-- url     : https://prove2.me/submissions/fec595d8-f583-4a71-8b5e-bb235535be8b

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set Complex Topology Kyprianou.Ch05
open scoped NNReal ENNReal Topology Classical
set_option autoImplicit false
theorem solution
    (t : NNReal) (ht : 0 < t) :
    (⋂ r > OrderDual.toDual t, Ioc ((OrderDual.ofDual r : NNReal) : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ)) =
      ({(t : ℝ)} : Set ℝ) ×ˢ Ioi (0 : ℝ) := by
  let R (s : NNRealᵒᵈ) := Ioc ((OrderDual.ofDual s : NNReal) : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ)
  let D := ({(t : ℝ)} : Set ℝ) ×ˢ Ioi (0 : ℝ)
  change (⋂ r > OrderDual.toDual t, R r) = D
  ext z
  constructor
  · intro hz
    have h0 := mem_iInter.mp (mem_iInter.mp hz (OrderDual.toDual (0 : NNReal))) ht
    refine ⟨?_,h0.2⟩
    apply mem_singleton_iff.mpr
    apply le_antisymm h0.1.2
    by_contra! hn
    let r := Real.toNNReal ((z.1+(t : ℝ))/2)
    have hr : (r : ℝ) = (z.1+(t : ℝ))/2 :=
      Real.coe_toNNReal _ (by linarith [h0.1.1,t.coe_nonneg])
    have hrt : r < t := by exact_mod_cast (show (r : ℝ) < (t : ℝ) by rw [hr]; linarith)
    have hh := mem_iInter.mp (mem_iInter.mp hz (OrderDual.toDual r)) hrt
    have hh' : (r : ℝ) < z.1 := hh.1.1
    rw [hr] at hh'
    linarith
  · intro hz
    refine mem_iInter.mpr fun r => mem_iInter.mpr fun hr => ?_
    have hrt : OrderDual.ofDual r < t := hr
    have hz' : z.1 = (t : ℝ) := hz.1
    exact ⟨⟨by rw [hz']; exact_mod_cast hrt,by rw [hz']⟩,hz.2⟩
