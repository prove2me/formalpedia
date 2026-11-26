-- Prove2me | solution 1 for Kyprianou.Ch05.killedPathRandomClockSurvivalV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:31:18.707288+00:00
-- url     : https://prove2.me/submissions/d53d04b9-9862-478f-953b-403182d93e2c

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_cadlagWholePathAEMeasurableOfCoordinatesV1
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
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
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → ℝ) (death : Omega → WithTop NNReal)
    (eta : ℝ) (hKilled : IsKilledSubordinator P Y death eta)
    (T : (NNReal → ℝ) → ENNReal) (hT : Measurable T)
    (C : Set (NNReal → ℝ)) (hC : MeasurableSet C) :
    P {w | (fun t => Y t w) ∈ C ∧ T (fun t => Y t w) < death w} =
      ∫⁻ f, if f ∈ C ∧ T f ≠ ⊤ then
        ENNReal.ofReal (Real.exp (-eta * (T f).toReal)) else 0
        ∂(P.map (fun w t => Y t w)) := by
  classical
  let W : Omega → (NNReal → ℝ) := fun w t => Y t w
  have hW : AEMeasurable W P :=
    Kyprianou.Ch02.cadlagWholePathAEMeasurableOfCoordinatesV1 P Y hKilled.1.1.cadlag_ae
      (Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P Y hKilled.1.1)
  have hd : Measurable death := hKilled.2.2.1
  haveI : IsProbabilityMeasure (P.map death) := Measure.isProbabilityMeasure_map hd.aemeasurable
  have hi : IndepFun death W P := hKilled.2.2.2.2.2
  have hmap := hi.symm.map_prod_eq_prod_map_map hW hd.aemeasurable
  let E : Set ((NNReal → ℝ) × WithTop NNReal) :=
    {z | z.1 ∈ C ∧ T z.1 < z.2}
  have hE : MeasurableSet E := (hC.preimage measurable_fst).inter
    (measurableSet_lt (hT.comp measurable_fst) measurable_snd)
  change P ((fun w => (W w,death w)) ⁻¹' E) = _
  rw [← Measure.map_apply_of_aemeasurable (hW.prodMk hd.aemeasurable) hE,
    hmap,Measure.prod_apply hE]
  apply lintegral_congr
  intro f
  by_cases hc : f ∈ C
  · by_cases ht : T f = ⊤
    · have he : Prod.mk f ⁻¹' E = ∅ := by
        ext e
        change (f ∈ C ∧ T f < e) ↔ False
        rw [ht]
        exact iff_false_intro (fun h => not_lt_of_ge le_top h.2)
      rw [he,measure_empty,if_neg (fun h => h.2 ht)]
    · let u : NNReal := (T f).toNNReal
      have hcoe : (u : ENNReal) = T f := ENNReal.coe_toNNReal ht
      have he : Prod.mk f ⁻¹' E = Ioi (u : WithTop NNReal) := by
        ext e
        change (f ∈ C ∧ T f < (e : ENNReal)) ↔ (u : WithTop NNReal) < e
        rw [← hcoe]
        exact and_iff_right hc
      rw [he,Measure.map_apply hd measurableSet_Ioi,if_pos ⟨hc,ht⟩]
      have hs := hKilled.2.2.2.2.1 u
      change P (death ⁻¹' Ioi (u : WithTop NNReal)) =
        ENNReal.ofReal (Real.exp (-eta * (u : ℝ))) at hs
      exact hs
  · simp [E,hc]
