-- Prove2me | solution 1 for Kyprianou.Ch05.pointFamilyJointRestrictedIntegralMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:26:55.623441+00:00
-- url     : https://prove2.me/submissions/f3c9abf3-fbed-4286-905a-58984330d416

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_pointFamilyPairLIntegralV1
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
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (K : ℕ → Omega → ℕ) (Z : ℕ → ℕ → Omega → E)
    (hK : ∀ k, Measurable (K k)) (hZ : ∀ k n, Measurable (Z k n))
    (g : Omega × E → ENNReal) (hg : Measurable g)
    (S : Set E) (hS : MeasurableSet S) :
    Measurable (fun w => ∫⁻ z in S, g (w,z) ∂(poissonRandomMeasure K Z w)) := by
  classical
  let G (i : ℕ × ℕ) (w : Omega) :=
    if i.2 < K i.1 w then S.indicator (fun z => g (w,z)) (Z i.1 i.2 w) else 0
  have he (w : Omega) : (∫⁻ z in S, g (w,z) ∂(poissonRandomMeasure K Z w)) =
      ∑' i, G i w := by
    rw [← lintegral_indicator hS]
    exact pointFamilyPairLIntegralV1 K Z w _ ((hg.comp measurable_prodMk_left).indicator hS)
  simp_rw [he]
  apply Measurable.tsum
  intro i
  have hm : Measurable (fun w => g (w,Z i.1 i.2 w)) :=
    hg.comp (measurable_id.prodMk (hZ i.1 i.2))
  have hs : MeasurableSet {w | Z i.1 i.2 w ∈ S} := hS.preimage (hZ i.1 i.2)
  have hn : MeasurableSet {w | i.2 < K i.1 w} := measurableSet_lt measurable_const (hK i.1)
  have hG : Measurable (fun w => if i.2 < K i.1 w then
      if Z i.1 i.2 w ∈ S then g (w,Z i.1 i.2 w) else 0 else 0) :=
    Measurable.ite hn (Measurable.ite hs hm measurable_const) measurable_const
  simpa only [G,Set.indicator] using hG
