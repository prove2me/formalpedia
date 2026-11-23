-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_unbounded_triplet_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T20:32:38.691427+00:00
-- url     : https://prove2.me/submissions/3f08cba6-660c-444b-a5e1-ae2da3d91129

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_law_positive_mgf
set_option autoImplicit false
open MeasureTheory Filter Set
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB
noncomputable section

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (θ : ℝ) (hθ : 0 < θ) :
    ψ θ / θ = D.triplet.drift + D.gaussianCoefficient ^ 2 * θ / 2 +
      ∫ y in Iio (0 : ℝ),
        (Real.exp (θ * y) - 1 - (if -1 < y then θ * y else 0)) / θ
          ∂D.triplet.levyMeasure := by
  let μ : Measure ℝ := D.triplet.levyMeasure
  let K : ℝ → ℝ := fun y => Real.exp (θ * y) - 1 - (if -1 < y then θ * y else 0)
  have hμneg : ∀ᵐ y ∂μ, y ∈ Iio (0 : ℝ) := by
    rw [ae_iff]
    simpa [μ, Set.Ici, Set.Iio, not_lt] using D.negativeJumps
  have hμeq : μ.restrict (Iio (0 : ℝ)) = μ :=
    Measure.restrict_eq_self_of_ae_mem hμneg
  have hψθ : ψ θ = tripletLaplace (-D.triplet.drift) D.gaussianCoefficient μ θ := by
    have hh := hψ θ 1 hθ.le (by norm_num)
    obtain ⟨-, hm⟩ := source_result81_law_positive_mgf Ω P D 1 θ hθ.le
    have hm' :
        (∫ ω : Ω, Real.exp (θ * (SpectrallyNegativeModel.toData P D).X 1 ω)
            ∂(SpectrallyNegativeModel.toData P D).law) =
          Real.exp ((1 : ℝ) *
            tripletLaplace (-D.triplet.drift) D.gaussianCoefficient D.triplet.levyMeasure θ) := by
      simpa [SpectrallyNegativeModel.toData] using hm
    rw [hh.2, hm']
    simp [μ]
  have hfull :
      (∫ x : ℝ, Real.exp (θ * x) - 1 - (if -1 < x then θ * x else 0) ∂μ) =
        ∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 - (if -1 < y then θ * y else 0) ∂μ := by
    change (∫ x : ℝ, Real.exp (θ * x) - 1 - (if -1 < x then θ * x else 0) ∂μ) =
      ∫ x : ℝ, Real.exp (θ * x) - 1 - (if -1 < x then θ * x else 0) ∂(μ.restrict (Iio (0 : ℝ)))
    rw [hμeq]
  have hdiv : (∫ y in Iio (0 : ℝ), K y ∂μ) / θ =
      ∫ y in Iio (0 : ℝ), K y / θ ∂μ := by
    rw [integral_div]
  rw [hψθ, tripletLaplace, hfull, ← hdiv]
  field_simp [hθ.ne']
  ring
