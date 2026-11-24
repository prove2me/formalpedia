-- Prove2me | solution 1 for Kyprianou.Ch02.subordinatorMarginalSufficiencyV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:46:01.043831+00:00
-- url     : https://prove2.me/submissions/936cfd68-7757-453f-b7d4-e8158b5056d4

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent

import Theorems.Thm_Kyprianou_Ch02_subordinatorUncompensatedExponentV1
import Theorems.Thm_Kyprianou_Ch02_subordinatorPoissonMarginalLawV1
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

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
            ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ)) :
    (levyMeasure (Set.Iio (0 : ℝ)) = 0 ∧
    σ = 0 ∧
    Integrable (fun x : ℝ => min (1 : ℝ) |x|)
      (levyMeasure.restrict (Set.Ioi (0 : ℝ))) ∧
    0 ≤ -a - ∫ x in Set.Ioo (0 : ℝ) 1, x ∂levyMeasure) →
    (∀ t : ℝ≥0, ∀ᵐ ω ∂P, 0 ≤ X t ω) := by
  rintro ⟨hs, hσ, hint, hd⟩ t
  have hmx : AEMeasurable (X t) P := by
    have h := (hX.stationary_increments 0 t).aemeasurable_snd
    have heq : increment X 0 t = X t := by
      funext omega
      change X t omega - X 0 omega = X t omega
      rw [congrFun hX.start_zero omega, sub_zero]
    rw [heq] at h
    exact h
  letI : IsProbabilityMeasure (P.map (X t)) := Measure.isProbabilityMeasure_map hmx
  obtain ⟨Q, hQ, hQzero, hQc⟩ :=
    Kyprianou.Ch02.subordinatorPoissonMarginalLawV1 levyMeasure hlevyMeasure hint t _ hd
  letI : IsProbabilityMeasure Q := hQ
  have hEq : P.map (X t) = Q := by
    apply Measure.ext_of_charFun
    funext ξ
    rw [hchar t ξ, hQc ξ,
      Kyprianou.Ch02.subordinatorUncompensatedExponentV1
        a σ levyMeasure hlevyMeasure hs hσ hint ξ]
  rw [← hEq, Measure.map_apply_of_aemeasurable hmx measurableSet_Iio] at hQzero
  rw [ae_iff]
  have hset : X t ⁻¹' Set.Iio (0 : ℝ) = {omega | X t omega < 0} := by
    ext omega
    rfl
  rw [hset] at hQzero
  simpa only [not_le] using hQzero
