-- Prove2me | solution 1 for Kyprianou.Ch02.levyMonotoneMarginalProbabilityFamilyV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:50:14.217794+00:00
-- url     : https://prove2.me/submissions/bb81f515-6899-4357-b9be-0ed35bf973d4

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false
open Filter Topology Set

theorem solution
    (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ))
    (hm : ∀ᵐ ω ∂P, Monotone (fun t : ℝ≥0 => X t ω)) :
    ∃ M : {t : ℝ // 0 < t} → ProbabilityMeasure ℝ,
      (∀ t ξ, charFun (M t : Measure ℝ) ξ =
        Complex.exp (((t.val : ℝ) : ℂ) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ)) ∧
      ∀ t, (M t : Measure ℝ) (Set.Iio (0 : ℝ)) = 0 := by
  have hmx (t : ℝ≥0) : AEMeasurable (X t) P := by
    have h := (hX.stationary_increments 0 t).aemeasurable_snd
    have heq : increment X 0 t = X t := by
      funext omega
      change X t omega - X 0 omega = X t omega
      rw [congrFun hX.start_zero omega, sub_zero]
    rw [heq] at h
    exact h
  let time (t : {t : ℝ // 0 < t}) : ℝ≥0 := ⟨t.val, le_of_lt t.property⟩
  let M (t : {t : ℝ // 0 < t}) : ProbabilityMeasure ℝ :=
    ⟨P.map (X (time t)), Measure.isProbabilityMeasure_map (hmx (time t))⟩
  refine ⟨M, ?_, ?_⟩
  · intro t ξ
    exact hchar (time t) ξ
  · intro t
    change P.map (X (time t)) (Set.Iio (0 : ℝ)) = 0
    rw [Measure.map_apply_of_aemeasurable (hmx (time t)) measurableSet_Iio]
    have hnonneg : ∀ᵐ omega ∂P, 0 ≤ X (time t) omega := by
      filter_upwards [hm] with omega hmono
      have hh := hmono (show (0 : ℝ≥0) ≤ time t from zero_le)
      simpa [congrFun hX.start_zero omega] using hh
    rw [ae_iff] at hnonneg
    have heq : X (time t) ⁻¹' Set.Iio (0 : ℝ) =
        {omega | ¬ 0 ≤ X (time t) omega} := by
      ext omega
      simp [not_le]
    rw [heq]
    exact hnonneg
