-- Prove2me | solution 1 for Kyprianou.Ch05.jumpPotentialInnerKernelMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:04:57.666341+00:00
-- url     : https://prove2.me/submissions/f08d93a2-9d0e-46ad-9edc-39feb4bb0324

import Mathlib
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
    (Pi : Measure ℝ) [SigmaFinite Pi]
    (x : ℝ) (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Measurable (fun v : ℝ => ∫⁻ z in Ioi (x-v),
      if z-(x-v) ∈ A ∧ x-v ∈ B then (1 : ENNReal) else 0 ∂Pi) := by
  classical
  let C : Set (ℝ × ℝ) := {p | x-p.1 < p.2 ∧ p.2-(x-p.1) ∈ A ∧ x-p.1 ∈ B}
  have hC : MeasurableSet C := (measurableSet_lt (measurable_const.sub measurable_fst)
    measurable_snd).inter ((hA.preimage (measurable_snd.sub (measurable_const.sub measurable_fst))).inter
    (hB.preimage (measurable_const.sub measurable_fst)))
  have hk : Measurable (fun v : ℝ => ∫⁻ z, C.indicator (fun _ => (1 : ENNReal)) (v,z) ∂Pi) :=
    (measurable_const.indicator hC).lintegral_prod_right'
  convert hk using 1
  funext v
  rw [← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro z
  simp only [Set.indicator,Set.mem_Ioi,C,Set.mem_setOf_eq]
  split_ifs <;> simp_all
