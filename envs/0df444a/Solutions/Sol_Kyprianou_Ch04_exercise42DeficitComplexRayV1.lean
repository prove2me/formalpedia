-- Prove2me | solution 1 for Kyprianou.Ch04.exercise42DeficitComplexRayV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T22:58:07.02196+00:00
-- url     : https://prove2.me/submissions/de5d95dd-e917-492c-b520-72167fd3d9d2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
import Theorems.Thm_Kyprianou_Ch02_nonnegativeLawComplexLaplaceAnalyticV1
import Theorems.Thm_Kyprianou_Ch02_subordinatorExponentComplexLaplaceAnalyticV1
import Theorems.Thm_Kyprianou_Ch04_rightHalfPlaneIdentityFromRealRayV1
import Theorems.Thm_Kyprianou_Ch04_exercise42ReflectedJumpMeasureV1
import Theorems.Thm_Kyprianou_Ch04_exercise42DeficitRealRayV1
open MeasureTheory Set AvramDividend.Classical Complex Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The actual drift deficit has its expected complex Laplace transform. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (L : SpectrallyNegativeLevy P F) (hBV : L.BoundedVariation)
    (t : ℝ≥0) (z : ℂ) (hz : 0 ≤ z.re) :
    (∫ ω, Complex.exp (-z * ((L.drift * (t : ℝ) - L.X t ω : ℝ) : ℂ)) ∂P) =
      Complex.exp (-((t : ℝ) : ℂ) *
        ∫ y in Iio (0 : ℝ), (1 - Complex.exp (z * (y : ℂ))) ∂L.ν) := by
  let : IsProbabilityMeasure P := L.isProbability
  let Z : Ω → ℝ := fun ω => L.drift * (t : ℝ) - L.X t ω
  have hZ : Measurable Z := measurable_const.sub L.adapted.measurable
  let Q := P.map Z
  let : IsProbabilityMeasure Q := Measure.isProbabilityMeasure_map hZ.aemeasurable
  have hpos : ∀ᵐ ω ∂P, 0 ≤ Z ω := by
    filter_upwards [bv_drift_deficit_ae_monotone_all_times L hBV] with ω hm
    have h := hm (show (0 : ℝ≥0) ≤ t from zero_le)
    simpa [Z, L.X_zero] using h
  have hQ : Q (Iio (0 : ℝ)) = 0 := by
    rw [show Q = P.map Z from rfl, Measure.map_apply hZ measurableSet_Iio]
    rw [ae_iff] at hpos
    have he : Z ⁻¹' Iio (0 : ℝ) = {ω | ¬ 0 ≤ Z ω} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_setOf_eq, not_le]
    rw [he]
    exact hpos
  let ν := (L.ν.restrict (Iio (0 : ℝ))).map (fun y : ℝ => -y)
  have hν := Kyprianou.Ch04.exercise42ReflectedJumpMeasureV1 P F L hBV
  let f : ℂ → ℂ := fun w => ∫ x, Complex.exp (-w * (x : ℂ)) ∂Q
  let g : ℂ → ℂ := fun w => Complex.exp (-((t : ℝ) : ℂ) *
    ∫ x in Ioi (0 : ℝ), (1 - Complex.exp (-w * (x : ℂ))) ∂ν)
  have hG (w : ℂ) : g w = Complex.exp (-((t : ℝ) : ℂ) *
      ∫ y in Iio (0 : ℝ), (1 - Complex.exp (w * (y : ℂ))) ∂L.ν) :=
    congrArg (fun a : ℂ => Complex.exp (-((t : ℝ) : ℂ) * a)) (hν.2 w)
  have hf := (Kyprianou.Ch02.nonnegativeLawComplexLaplaceAnalyticV1 Q hQ).1
  have hg := (Kyprianou.Ch02.subordinatorExponentComplexLaplaceAnalyticV1 ν hν.1 0
    (le_refl 0) t).1
  have hg' : DiffContOnCl ℂ g {w : ℂ | 0 < w.re} := by simpa [g] using hg
  have hmap (w : ℂ) : f w =
      ∫ ω, Complex.exp (-w * (Z ω : ℂ)) ∂P :=
    integral_map hZ.aemeasurable (by fun_prop)
  have hreal (θ : ℝ) (hθ : 1 ≤ θ) : f (θ : ℂ) = g (θ : ℂ) := by
    rw [hmap, hG]
    simpa only [Z] using
      Kyprianou.Ch04.exercise42DeficitRealRayV1 P F L hBV t θ hθ
  have he := Kyprianou.Ch04.rightHalfPlaneIdentityFromRealRayV1 f g hf hg' hreal z hz
  rw [hmap, hG] at he
  exact he
