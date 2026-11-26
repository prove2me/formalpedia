-- Prove2me | solution 1 for Kyprianou.Ch05.canonicalPositivePoissonIndependentIncrementsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:26:39.679393+00:00
-- url     : https://prove2.me/submissions/e9c9a0a9-eaa4-45f6-9d3c-2cbad3dcc023

import Mathlib
import Theorems.Thm_ProbabilityTheory_iIndep_prmEvalSigma
import Theorems.Thm_Kyprianou_Ch05_pointFamilyRegionLintegralMeasurableV1
import Theorems.Thm_Kyprianou_Ch05_positivePoissonPathIncrementStripV1
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
    {Lambda : Type} [MeasurableSpace Lambda]
    (Q : Measure Lambda) [IsProbabilityMeasure Q]
    (Pi : Measure ℝ) [SigmaFinite Pi]
    (K : ℕ → Lambda → ℕ) (Z : ℕ → ℕ → Lambda → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod Pi) Q)
    (hint : Integrable (fun z : ℝ => min (1 : ℝ) |z|) Pi)
    (d : ℝ) :
    HasIndependentIncrements (fun (t : NNReal) (w : Lambda) =>
      d * (t : ℝ) + (∫⁻ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal) Q := by
  intro n t ht
  let R (i : Fin n) := Ioc (t i.castSucc : ℝ) (t i.succ : ℝ) ×ˢ Ioi (0 : ℝ)
  have hp : Pairwise (fun i j : Fin n => Disjoint (R i) (R j)) := by
    intro i j hij
    apply Set.disjoint_left.2
    intro z hi hj
    rcases lt_or_gt_of_ne hij with h|h
    · have hh : (t i.succ : ℝ) ≤ (t j.castSucc : ℝ) := by
        exact_mod_cast ht (Fin.succ_le_castSucc_iff.mpr h)
      exact (not_lt_of_ge (hi.1.2.trans hh)) hj.1.1
    · have hh : (t j.succ : ℝ) ≤ (t i.castSucc : ℝ) := by
        exact_mod_cast ht (Fin.succ_le_castSucc_iff.mpr h)
      exact (not_lt_of_ge (hj.1.2.trans hh)) hi.1.1
  let G (i : Fin n) (w : Lambda) := d*((t i.succ : ℝ)-(t i.castSucc : ℝ)) +
    (∫⁻ z in R i, ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal
  have hi : iIndepFun G Q := by
    apply (iIndepFun_iff_iIndep (fun _ : Fin n => (inferInstance : MeasurableSpace ℝ)) _ Q).2
    refine iIndep_of_iIndep_of_le (ProbabilityTheory.iIndep_prmEvalSigma hd hp) ?_
    intro i
    have hm := pointFamilyRegionLintegralMeasurableV1 ((volume : Measure ℝ).prod Pi)
      K Z (R i) (measurableSet_Ioc.prod measurableSet_Ioi)
      (fun z => ENNReal.ofReal z.2) (ENNReal.measurable_ofReal.comp measurable_snd)
    exact ((ENNReal.measurable_toReal.comp hm).const_add _).comap_le
  apply hi.congr
  intro i
  filter_upwards [positivePoissonPathIncrementStripV1 Q Pi K Z hd hint d] with w hw
  exact (hw (t i.castSucc) (t i.succ) (ht (Fin.castSucc_le_succ i))).symm
