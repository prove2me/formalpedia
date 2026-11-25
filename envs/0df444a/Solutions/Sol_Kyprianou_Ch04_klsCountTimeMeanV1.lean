-- Prove2me | solution 1 for Kyprianou.Ch04.klsCountTimeMeanV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:38:13.716262+00:00
-- url     : https://prove2.me/submissions/043883d6-1cc8-414a-b1bc-a7872200a9ea

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_CompensatedIsometry
import Theorems.Thm_Kyprianou_Ch02_prmFiniteIntensityCountRealL2V1
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A finite KLS Poisson time-mark count is integrable with its exact intensity mean. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : PoissonRandomMeasure.{0,0,0} P ν) (A : Set ℝ)
    (hA : MeasurableSet A) (hfinite : ν A < ⊤) (t : ℝ≥0) :
    let C := fun ω => (N.N ω (Ioc (0 : ℝ) (t : ℝ) ×ˢ A)).toReal
    Integrable C P ∧ (∫ ω, C ω ∂P) = (t : ℝ) * (ν A).toReal := by
  dsimp only
  let R := Ioc (0 : ℝ) (t : ℝ) ×ˢ A
  have hRef : referenceIntensity ν R = ENNReal.ofReal (t : ℝ) * ν A := by
    unfold R referenceIntensity
    rw [Measure.prod_prod, Measure.restrict_apply measurableSet_Ioc]
    have hsub : Ioc (0 : ℝ) (t : ℝ) ∩ Ici (0 : ℝ) = Ioc 0 (t : ℝ) :=
      Set.inter_eq_left.mpr fun _ hx => hx.1.le
    rw [hsub, Real.volume_Ioc, sub_zero]
  have hR : MeasurableSet R := measurableSet_Ioc.prod hA
  have hfin : referenceIntensity ν R ≠ ⊤ := by
    rw [hRef]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite.ne
  have hi := (Kyprianou.Ch02.prmFiniteIntensityCountRealL2V1 P ν N R hR hfin).integrable (by norm_num)
  refine ⟨hi,?_⟩
  have h := LevyStochCalc.Poisson.Compensated.compensated_mean_zero N hR hfin
  change (∫ ω, (N.N ω R).toReal - (referenceIntensity ν R).toReal ∂P) = 0 at h
  rw [integral_sub hi (integrable_const _), integral_const, probReal_univ, one_smul,
    hRef, ENNReal.toReal_mul, ENNReal.toReal_ofReal t.coe_nonneg] at h
  exact sub_eq_zero.mp h
