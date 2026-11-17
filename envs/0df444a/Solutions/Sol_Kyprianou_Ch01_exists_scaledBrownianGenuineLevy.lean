-- Prove2me | solution 1 for Kyprianou.Ch01.exists_scaledBrownianGenuineLevy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:11:16.584334+00:00
-- url     : https://prove2.me/submissions/05cf488f-0980-4cac-a6da-68fba3a4211c

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_KLSModular_BrownianMotion_Gaussian_BrownianMotion
import Theorems.Thm_ProbabilityTheory_isBrownianReal_brownian_avram
import Theorems.Thm_Kyprianou_Ch01_isBrownianReal_toStrictLevyProcess
import Theorems.Thm_Kyprianou_Ch01_isLevyProcess_realScale
import Theorems.Thm_Kyprianou_Ch01_charFun_scaledBrownianZeroStart
import Theorems.Thm_AvramDividend_Classical_canonical_drifted_brownian_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal
set_option autoImplicit false

theorem solution (v : ℝ≥0) :
    ∃ (Ω : Type) (m : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := m
      ∃ (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ),
        IsProbabilityMeasure P ∧ IsLevyProcess B P ∧
        (∀ t, Measurable (B t)) ∧
        ∀ (t : ℝ≥0) (xi : ℝ),
          charFun (P.map (B t)) xi =
            Complex.exp (-(((v : ℝ) * (t : ℝ) : ℂ) *
              (xi : ℂ) ^ 2 / 2)) := by
  classical
  let P : Measure (ℝ≥0 → ℝ) := gaussianLimit
  let B : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ :=
    fun t ω => Real.sqrt (v : ℝ) *
      (ProbabilityTheory.brownian t ω - ProbabilityTheory.brownian 0 ω)
  refine ⟨ℝ≥0 → ℝ, inferInstance, P, B, ?_, ?_, ?_, ?_⟩
  · infer_instance
  · have hbase : IsLevyProcess
        (fun t ω => ProbabilityTheory.brownian t ω -
          ProbabilityTheory.brownian 0 ω) P :=
      Kyprianou.Ch01.isBrownianReal_toStrictLevyProcess
        P ProbabilityTheory.brownian
        ProbabilityTheory.isBrownianReal_brownian_avram
    exact Kyprianou.Ch01.isLevyProcess_realScale
      P (fun t ω => ProbabilityTheory.brownian t ω -
        ProbabilityTheory.brownian 0 ω)
      (Real.sqrt (v : ℝ)) hbase
  · intro t
    have hm := AvramDividend.Classical.canonical_drifted_brownian_measurable t
    have hm' : Measurable (fun ω : ℝ≥0 → ℝ =>
        ProbabilityTheory.brownian t ω -
          ProbabilityTheory.brownian 0 ω) := by
      have hplus := hm.add
        (measurable_const : Measurable (fun _ : ℝ≥0 → ℝ => (t : ℝ)))
      have hfun :
          ((fun ω : ℝ≥0 → ℝ =>
            ProbabilityTheory.brownian t ω -
              ProbabilityTheory.brownian 0 ω - (t : ℝ)) +
            (fun _ : ℝ≥0 → ℝ => (t : ℝ))) =
          (fun ω : ℝ≥0 → ℝ =>
            ProbabilityTheory.brownian t ω -
              ProbabilityTheory.brownian 0 ω) := by
        funext omega
        dsimp
        ring
      rw [hfun] at hplus
      exact hplus
    exact measurable_const.mul hm'
  · intro t xi
    exact Kyprianou.Ch01.charFun_scaledBrownianZeroStart
      P ProbabilityTheory.brownian
      ProbabilityTheory.isBrownianReal_brownian_avram v t xi
