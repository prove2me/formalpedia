-- Prove2me | solution 1 for Kyprianou.Ch03.rawEsscherPastLIntegralFactorV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:19:21.720096+00:00
-- url     : https://prove2.me/submissions/50d13b35-a917-46a4-88ef-92a98def537b

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
import Theorems.Thm_Kyprianou_Ch01_levyIncrement_indep_naturalSigma
import Theorems.Thm_Kyprianou_Ch01_naturalSigma_eq_natFiltr
import Theorems.Thm_Kyprianou_Ch03_esscherDensity_factorAtTimes
import Theorems.Thm_Kyprianou_Ch03_rawEsscherIncrementFactorMeanV1
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (beta : ℝ) (hm : ∀ t, Measurable (X t)) (k : ℝ)
    (hunit : ∀ t : NNReal, Integrable (esscherDensity X beta k t) P ∧
      (∫ w, esscherDensity X beta k t w ∂P) = 1) :
    ∀ s t : NNReal, s ≤ t → ∀ A,
      MeasurableSet[PerfCorrMSQ.natFiltr X s] A →
      (∫⁻ w, A.indicator (fun w => ENNReal.ofReal (esscherDensity X beta k t w)) w ∂P) =
        (∫⁻ w, A.indicator (fun w => ENNReal.ofReal (esscherDensity X beta k s w)) w ∂P) := by
  have hle (u : NNReal) : PerfCorrMSQ.natFiltr X u ≤ (inferInstance : MeasurableSpace Ω) :=
    iSup₂_le fun v _ => (hm v).comap_le
  intro s t hst B hB
  let Z : NNReal → Ω → ℝ≥0∞ := fun u w => ENNReal.ofReal (esscherDensity X beta k u w)
  let W : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (beta * y - k * ((t - s : NNReal) : ℝ)))
  have hXs : Measurable[PerfCorrMSQ.natFiltr X s] (X s) :=
    measurable_iff_comap_le.mpr (le_iSup₂_of_le s le_rfl le_rfl)
  have hZ : Measurable[PerfCorrMSQ.natFiltr X s] (Z s) :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp ((hXs.const_mul beta).sub measurable_const))
  have hW : Measurable W := by fun_prop
  have hfac : B.indicator (Z t) =
      fun w => W (X t w - X s w) * B.indicator (Z s) w := by
    funext w
    by_cases hw : w ∈ B
    · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw]
      dsimp only [Z, W]
      rw [Kyprianou.Ch03.esscherDensity_factorAtTimes X beta k s t w, NNReal.coe_sub hst,
        ENNReal.ofReal_mul (show 0 ≤ esscherDensity X beta k s w from (Real.exp_pos _).le), mul_comm]
    · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw, mul_zero]
  have hind := Kyprianou.Ch01.levyIncrement_indep_naturalSigma P X hX hm s t hst
  rw [Kyprianou.Ch01.naturalSigma_eq_natFiltr] at hind
  have hf : Measurable[MeasurableSpace.comap (fun w => X t w - X s w) inferInstance]
      (fun w => W (X t w - X s w)) := hW.comp (Measurable.of_comap_le le_rfl)
  have hmul := lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    ((hm t).sub (hm s)).comap_le (hle s) hind hf (hZ.indicator hB)
  have hWI : ∫⁻ w, W (X t w - X s w) ∂P = 1 :=
    Kyprianou.Ch03.rawEsscherIncrementFactorMeanV1 P X hX beta hm k hunit s t hst
  change (∫⁻ w, B.indicator (Z t) w ∂P) = ∫⁻ w, B.indicator (Z s) w ∂P
  rw [hfac, hmul, hWI, one_mul]
