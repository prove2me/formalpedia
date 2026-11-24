-- Prove2me | solution 1 for Kyprianou.Ch02.subordinatorComplexLaplaceFromTripletV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:53:26.285796+00:00
-- url     : https://prove2.me/submissions/3c21a03f-0ed1-4ccb-99d7-f649607ecc38

import Theorems.Thm_Kyprianou_Ch02_boundedRightHalfPlaneZeroPublicV1
import Theorems.Thm_Kyprianou_Ch02_nonnegativeLawComplexLaplaceAnalyticV1
import Theorems.Thm_Kyprianou_Ch02_subordinatorExponentComplexLaplaceAnalyticV1
import Theorems.Thm_Kyprianou_Ch02_subordinatorComplexLaplaceImaginaryBoundaryV1
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Theorems.Thm_Kyprianou_Ch02_subordinatorUncompensatedExponentV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (τ : ℝ≥0 → Ω → ℝ≥0)
    (aτ : ℝ) (στ : ℝ≥0) (ντ : Measure ℝ)
    (hντ : ProbabilityTheory.IsLevyMeasure ντ)
    (hτ : ProbabilityTheory.IsLevyProcess
       (fun t ω => (τ t ω : ℝ)) P)
    (hτchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (fun ω => (τ t ω : ℝ))) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-aτ, στ ^ 2, ντ, hντ⟩ ξ))
    (hneg : ντ (Set.Iio (0 : ℝ)) = 0)
    (hsigma : στ = 0)
    (hint : Integrable (fun x : ℝ => min (1 : ℝ) |x|)
      (ντ.restrict (Set.Ioi (0 : ℝ))))
    (hdis : 0 ≤ -aτ - ∫ x in Set.Ioo (0 : ℝ) 1, x ∂ντ) :
    let d : ℝ := -aτ - ∫ x in Set.Ioo (0 : ℝ) 1, x ∂ντ
    let Ξ : ℂ → ℂ := fun z =>
      (d : ℂ) * z +
      ∫ x in Set.Ioi (0 : ℝ),
        (1 - Complex.exp (-z * ((x : ℝ) : ℂ))) ∂ντ
    ∀ (t : ℝ≥0) (z : ℂ), 0 ≤ z.re →
      ∫ ω, Complex.exp (-z * (((τ t ω : ℝ) : ℂ))) ∂P =
        Complex.exp (-(((t : ℝ) : ℂ)) * Ξ z) := by
  dsimp only
  let d : ℝ := -aτ - ∫ x in Set.Ioo (0 : ℝ) 1, x ∂ντ
  let Ξ : ℂ → ℂ := fun z => (d : ℂ) * z +
    ∫ x in Set.Ioi (0 : ℝ), (1 - Complex.exp (-z * (x : ℂ))) ∂ντ
  intro t z hz
  let Z : Ω → ℝ := fun ω => (τ t ω : ℝ)
  have hZ : AEMeasurable Z P :=
    Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P _ hτ t
  let Q := P.map Z
  letI : IsProbabilityMeasure Q := Measure.isProbabilityMeasure_map hZ
  have hQ : Q (Set.Iio (0 : ℝ)) = 0 := by
    rw [show Q = P.map Z from rfl, Measure.map_apply_of_aemeasurable hZ measurableSet_Iio]
    have he : Z ⁻¹' Set.Iio (0 : ℝ) = ∅ := by
      ext ω
      simp [Z, not_lt_of_ge (τ t ω).coe_nonneg]
    rw [he, measure_empty]
  have hchar (ξ : ℝ) : charFun Q ξ =
      Complex.exp ((((t : ℝ) : ℂ)) *
        (Complex.I * ((d * ξ : ℝ) : ℂ) +
          ∫ x in Set.Ioi (0 : ℝ),
            (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂ντ)) := by
    change charFun (P.map (fun ω => (τ t ω : ℝ))) ξ = _
    rw [hτchar, Kyprianou.Ch02.subordinatorUncompensatedExponentV1
      aτ στ ντ hντ hneg hsigma hint ξ]
  let f : ℂ → ℂ := fun w => ∫ x, Complex.exp (-w * (x : ℂ)) ∂Q
  let g : ℂ → ℂ := fun w => Complex.exp (-(((t : ℝ) : ℂ)) * Ξ w)
  have hf := Kyprianou.Ch02.nonnegativeLawComplexLaplaceAnalyticV1 Q hQ
  have hg := Kyprianou.Ch02.subordinatorExponentComplexLaplaceAnalyticV1 ντ hint d hdis t
  have hbd : ∀ w : ℂ, 0 ≤ w.re → ‖f w - g w‖ ≤ 2 := by
    intro w hw
    exact (norm_sub_le _ _).trans (by
      have hfw : ‖f w‖ ≤ 1 := hf.2 w hw
      have hgw : ‖g w‖ ≤ 1 := hg.2 w hw
      linarith)
  have hzero : ∀ y : ℝ, f ((y : ℂ) * Complex.I) - g ((y : ℂ) * Complex.I) = 0 := by
    intro y
    exact sub_eq_zero.2
      (Kyprianou.Ch02.subordinatorComplexLaplaceImaginaryBoundaryV1 Q ντ d t hchar y)
  have heq : f z = g z := sub_eq_zero.1
    (Kyprianou.Ch02.boundedRightHalfPlaneZeroPublicV1 (fun w => f w - g w)
      (hf.1.sub hg.1) 2 hbd hzero z hz)
  change (∫ ω, Complex.exp (-z * (Z ω : ℂ)) ∂P) = g z
  rw [← heq]
  exact (integral_map hZ (by fun_prop : AEStronglyMeasurable
    (fun x : ℝ => Complex.exp (-z * (x : ℂ))) Q)).symm

