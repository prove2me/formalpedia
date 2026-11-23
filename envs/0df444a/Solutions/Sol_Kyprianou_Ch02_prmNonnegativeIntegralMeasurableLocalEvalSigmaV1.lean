-- Prove2me | solution 1 for Kyprianou.Ch02.prmNonnegativeIntegralMeasurableLocalEvalSigmaV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:41:27.897324+00:00
-- url     : https://prove2.me/submissions/d8753b33-6ced-4587-abcd-171776a874a0

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (R : Set (ℝ × ℝ)) (hRm : MeasurableSet R)
    (g : ℝ × ℝ → ℝ≥0∞) (hg : Measurable g)
    (hgR : ∀ z ∉ R, g z = 0) :
    Measurable[(⨆ C ∈ {C : Set (ℝ × ℝ) | C ⊆ R ∧ MeasurableSet C},
        MeasurableSpace.comap (fun ω => N.N ω C) inferInstance)]
      (fun ω => ∫⁻ z, g z ∂(N.N ω)) := by
  have hEval (C : Set (ℝ × ℝ)) (hC : MeasurableSet C) (hCR : C ⊆ R) :
      Measurable[(⨆ C ∈ {C : Set (ℝ × ℝ) | C ⊆ R ∧ MeasurableSet C},
        MeasurableSpace.comap (fun ω => N.N ω C) inferInstance)] (fun ω => N.N ω C) :=
    Measurable.of_comap_le
      (le_iSup₂_of_le C ⟨hCR, hC⟩ le_rfl)
  have hfiber : ∀ (n : ℕ) {y : ℝ≥0∞}, y ≠ 0 →
      SimpleFunc.eapprox g n ⁻¹' {y} ⊆ R := by
    intro n y hy z hz
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hz
    by_contra hzR
    have hle : SimpleFunc.eapprox g n z ≤ g z := by
      have h := le_iSup (fun k => SimpleFunc.eapprox g k z) n
      rwa [SimpleFunc.iSup_eapprox_apply hg z] at h
    rw [hz, hgR z hzR, le_zero_iff] at hle
    exact hy hle
  have hsimple : ∀ n : ℕ, Measurable[(⨆ C ∈ {C : Set (ℝ × ℝ) | C ⊆ R ∧ MeasurableSet C},
        MeasurableSpace.comap (fun ω => N.N ω C) inferInstance)]
      (fun ω => (SimpleFunc.eapprox g n).lintegral (N.N ω)) := by
    intro n
    simp only [SimpleFunc.lintegral]
    refine Finset.measurable_sum _ fun y _ => ?_
    by_cases hy : y = 0
    · simp only [hy, zero_mul]
      exact measurable_const
    · exact (hEval ((SimpleFunc.eapprox g n) ⁻¹' {y})
        ((SimpleFunc.eapprox g n).measurableSet_fiber y)
        (hfiber n hy)).const_mul y
  have hcongr : (fun ω => ∫⁻ z, g z ∂(N.N ω))
      = fun ω => ⨆ n : ℕ, (SimpleFunc.eapprox g n).lintegral (N.N ω) :=
    funext fun ω => lintegral_eq_iSup_eapprox_lintegral hg
  rw [hcongr]
  exact Measurable.iSup hsimple
