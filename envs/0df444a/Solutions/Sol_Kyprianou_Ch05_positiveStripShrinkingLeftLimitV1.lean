-- Prove2me | solution 1 for Kyprianou.Ch05.positiveStripShrinkingLeftLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:27:33.417907+00:00
-- url     : https://prove2.me/submissions/c0b0f173-1586-4c21-8ed3-ac3e58e3c66d

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_positiveStripShrinkingLeftIntersectionV1
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
    (mu : Measure (ℝ × ℝ)) (t : NNReal) (ht : 0 < t)
    (hf : (∫⁻ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ),
      ENNReal.ofReal z.2 ∂mu) < ⊤) :
    Tendsto (fun s : NNReal => (∫⁻ z in Ioc (s : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ),
      ENNReal.ofReal z.2 ∂mu).toReal) (nhdsWithin t (Iio t))
      (nhds ((∫⁻ z in {(t : ℝ)} ×ˢ Ioi (0 : ℝ), ENNReal.ofReal z.2 ∂mu).toReal)) := by
  let nu := mu.withDensity (fun z => ENNReal.ofReal z.2)
  let R (s : NNRealᵒᵈ) := Ioc ((OrderDual.ofDual s : NNReal) : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ)
  let D := ({(t : ℝ)} : Set ℝ) ×ˢ Ioi (0 : ℝ)
  have hR (s : NNRealᵒᵈ) : MeasurableSet (R s) := measurableSet_Ioc.prod measurableSet_Ioi
  have he : (⋂ r > OrderDual.toDual t, R r) = D :=
    positiveStripShrinkingLeftIntersectionV1 t ht
  have hm : ∀ i j : NNRealᵒᵈ, OrderDual.toDual t < i → i ≤ j → R i ⊆ R j := by
    intro i j _ hij z hz
    have hji : OrderDual.ofDual j ≤ OrderDual.ofDual i := hij
    exact ⟨⟨lt_of_le_of_lt (by exact_mod_cast hji) hz.1.1,hz.1.2⟩,hz.2⟩
  have hfin : nu (R (OrderDual.toDual 0)) ≠ ⊤ := by
    rw [show nu (R (OrderDual.toDual 0)) = _ from withDensity_apply _ (hR _)]
    exact hf.ne
  have hD : MeasurableSet D := (measurableSet_singleton _).prod measurableSet_Ioi
  have hDfin : nu D ≠ ⊤ := by
    apply ne_top_of_le_ne_top hfin
    apply measure_mono
    intro z hz
    exact ⟨⟨by rw [show z.1 = (t : ℝ) from hz.1]; exact_mod_cast ht,
      by rw [show z.1 = (t : ℝ) from hz.1]⟩,hz.2⟩
  have h := tendsto_measure_biInter_gt (μ := nu) (a := OrderDual.toDual t)
    (s := R) (fun r _ => (hR r).nullMeasurableSet) hm
    ⟨OrderDual.toDual 0,ht,hfin⟩
  rw [he] at h
  have hlim := (ENNReal.tendsto_toReal hDfin).comp h
  change Tendsto (fun s : NNReal => (nu (R (OrderDual.toDual s))).toReal)
    (nhdsWithin t (Iio t)) (nhds (nu D).toReal) at hlim
  have hs (s : NNReal) : nu (R (OrderDual.toDual s)) =
      ∫⁻ z in Ioc (s : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ), ENNReal.ofReal z.2 ∂mu :=
    withDensity_apply _ (hR _)
  have hd : nu D = ∫⁻ z in {(t : ℝ)} ×ˢ Ioi (0 : ℝ), ENNReal.ofReal z.2 ∂mu :=
    withDensity_apply _ hD
  simp only [hs,hd] at hlim
  exact hlim
