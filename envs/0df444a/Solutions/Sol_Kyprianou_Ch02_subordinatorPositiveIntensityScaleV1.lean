-- Prove2me | solution 1 for Kyprianou.Ch02.subordinatorPositiveIntensityScaleV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:59:19.490041+00:00
-- url     : https://prove2.me/submissions/e56db508-e28f-407a-9f04-f698f08961a8

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_ProbabilityTheory_IsLevyMeasure_sigmaFinite
import Theorems.Thm_Kyprianou_Ch02_poissonNonnegativeIntegralLawV1
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (ν : Measure ℝ) (hν : ProbabilityTheory.IsLevyMeasure ν)
    (hint : Integrable (fun x : ℝ => min (1 : ℝ) |x|)
      (ν.restrict (Set.Ioi (0 : ℝ)))) (t : ℝ≥0) :
    ∃ Q : Measure ℝ, IsProbabilityMeasure Q ∧ Q (Set.Iio (0 : ℝ)) = 0 ∧
      ∀ ξ : ℝ, charFun Q ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          ∫ x in Set.Ioi (0 : ℝ), (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂ν) := by
  letI : SigmaFinite ν := hν.sigmaFinite
  let m : Measure ℝ := (t : ℝ≥0∞) • ν.restrict (Set.Ioi (0 : ℝ))
  letI : SigmaFinite m := by
    dsimp [m]
    infer_instance
  let f : ℝ → ℝ := fun x => max x 0
  have hf : Measurable f := measurable_id.max measurable_const
  have he : f =ᵐ[ν.restrict (Set.Ioi (0 : ℝ))] id := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact max_eq_left (le_of_lt hx)
  have hfi : Integrable (fun x => min (1 : ℝ) |f x|) m := by
    have hh : Integrable (fun x => min (1 : ℝ) |f x|) (ν.restrict (Set.Ioi (0 : ℝ))) :=
      hint.congr (he.mono fun x hx => by simp [hx])
    exact hh.smul_measure (by simp)
  obtain ⟨Q, hQ, hs, hchar⟩ :=
    Kyprianou.Ch02.poissonNonnegativeIntegralLawV1 m f hf (fun x => le_max_right x 0) hfi
  refine ⟨Q, hQ, hs, fun ξ => ?_⟩
  rw [hchar]
  congr 1
  rw [show m = (t : ℝ≥0∞) • ν.restrict (Set.Ioi (0 : ℝ)) from rfl, integral_smul_measure]
  have heq : (fun x : ℝ => Complex.exp (I * ((ξ * f x : ℝ) : ℂ)) - 1) =ᵐ[ν.restrict (Set.Ioi (0 : ℝ))]
      (fun x : ℝ => Complex.exp (I * ((ξ * x : ℝ) : ℂ)) - 1) := by
    filter_upwards [he] with x hx
    rw [show f x = x from hx]
  rw [integral_congr_ae heq]
  simp [Complex.real_smul]
