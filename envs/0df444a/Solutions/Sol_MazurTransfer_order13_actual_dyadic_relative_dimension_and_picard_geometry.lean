-- Prove2me | solution 1 for MazurTransfer.order13_actual_dyadic_relative_dimension_and_picard_geometry
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T05:34:20.47884+00:00
-- url     : https://prove2.me/submissions/cd43334f-c7f6-4e50-a5ff-c5d91f9c4545

import Mathlib
import Definitions.Def_MazurTransfer_Order13DyadicOriginalPicardZeroSectionData20261019
import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalCoefficientAndOverlapBaseChangeMapsData20261019
import Theorems.Thm_MazurTransfer_order13_mixed_quadratic_unit_and_smoothness_certificates
import Theorems.Thm_MazurTransfer_order13_actual_mixed_quadratic_both_field_chart_domains
import Theorems.Thm_MazurTransfer_order13_actual_mixed_quadratic_curve_proper
import Theorems.Thm_MazurTransfer_order13_actual_mixed_curve_geometricallyIntegral
import Theorems.Thm_MazurTransfer_mixed_quadratic_coordinate_kaehler_equiv
import Theorems.Thm_MazurTransfer_locally_standardSmooth_relativeDimension_one_of_kaehler_equiv
noncomputable section
open CategoryTheory AlgebraicGeometry MazurTransfer
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticGluedCurve
namespace MazurTransfer.DyadicPicardGeometryOriginalProofContext20261019
theorem originalDyadicGeometryPrimeProvider20261019 : Fact (Nat.Prime 2) := ⟨by decide⟩
end MazurTransfer.DyadicPicardGeometryOriginalProofContext20261019
attribute [local instance] MazurTransfer.DyadicPicardGeometryOriginalProofContext20261019.originalDyadicGeometryPrimeProvider20261019
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual ordinary and reciprocal affine mixed quadratic
schemes over Z localized at two, both smooth, flat and locally finitely
presented. Named downstream consumer: their gluing and comparison with
the existing rational order-thirteen curve. Proper gluing is separate.
-/
namespace MazurTransfer.Order13DyadicMixedQuadraticCharts
open Order13LocalIntegralCoefficientMaps
theorem dyadic_integer_unit (n : ℕ) (hn : ¬ (2 : ℤ) ∣ (n : ℤ)) :
    IsUnit (n : BaseRing) := by
  have h : (n : ℤ) ∈ (primeIdeal 2).primeCompl := by
    change (n : ℤ) ∉ Ideal.span {(2 : ℤ)}
    rw [Ideal.mem_span_singleton]
    exact hn
  simpa only [_root_.map_natCast] using IsLocalization.map_units BaseRing ⟨(n : ℤ), h⟩

theorem ordinary_algebra_smooth : Algebra.Smooth BaseRing (ordinaryCoordinateRing BaseRing) :=
  MazurTransfer.order13_mixed_quadratic_unit_and_smoothness_certificates.2.1 BaseRing (dyadic_integer_unit 117 (by norm_num))
theorem reciprocal_algebra_smooth : Algebra.Smooth BaseRing (reciprocalCoordinateRing BaseRing) :=
  MazurTransfer.order13_mixed_quadratic_unit_and_smoothness_certificates.2.2.2 BaseRing (dyadic_integer_unit 39 (by norm_num))

end MazurTransfer.Order13DyadicMixedQuadraticCharts
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the ACTUAL mixed quadratic chart rings over Z_(2) are
domains, by injectivity of their genuine rational scalar-extension maps.
Named downstream consumer: relative dimension one and Picard geometry at two.
-/
noncomputable section
namespace MazurTransfer.Order13DyadicMixedQuadraticChartDomains
open Algebra TensorProduct Polynomial
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticRationalChartComparison
open Order13MixedQuadraticCoefficientBaseChange Order13MixedQuadraticAffineBaseChange

theorem ordinaryRational_isDomain : IsDomain (ordinaryCoordinateRing ℚ) :=
  MazurTransfer.order13_actual_mixed_quadratic_both_field_chart_domains.1 ℚ

theorem reciprocalRational_isDomain : IsDomain (reciprocalCoordinateRing ℚ) :=
  MazurTransfer.order13_actual_mixed_quadratic_both_field_chart_domains.2 ℚ

theorem ordinaryRingMap_injective : Function.Injective (ordinaryRingMap BaseRing ℚ) := by
  letI : Algebra.Smooth BaseRing (ordinaryCoordinateRing BaseRing) := ordinary_algebra_smooth
  exact (ordinaryAlgebraEquiv BaseRing ℚ).injective.comp
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective BaseRing ℚ))

theorem reciprocalRingMap_injective : Function.Injective (reciprocalRingMap BaseRing ℚ) := by
  letI : Algebra.Smooth BaseRing (reciprocalCoordinateRing BaseRing) := reciprocal_algebra_smooth
  exact (reciprocalAlgebraEquiv BaseRing ℚ).injective.comp
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective BaseRing ℚ))

theorem ordinaryDyadic_isDomain : IsDomain (ordinaryCoordinateRing BaseRing) := by
  letI := ordinaryRational_isDomain
  exact Function.Injective.isDomain (ordinaryRingMap BaseRing ℚ) ordinaryRingMap_injective

theorem reciprocalDyadic_isDomain : IsDomain (reciprocalCoordinateRing BaseRing) := by
  letI := reciprocalRational_isDomain
  exact Function.Injective.isDomain (reciprocalRingMap BaseRing ℚ) reciprocalRingMap_injective

theorem base_isNoetherianRing : IsNoetherianRing BaseRing := inferInstance

end MazurTransfer.Order13DyadicMixedQuadraticChartDomains
end
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the genuine two dyadic chart Kaehler modules are free of
rank one, using the public mixed differential criterion and literal integral
Jacobian witnesses. Named downstream consumer: relative dimension one.
-/
noncomputable section
namespace MazurTransfer.Order13DyadicMixedQuadraticDifferentials
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticJacobianCertificates

theorem ordinary_kaehler_equiv :
    Nonempty (Ω[ordinaryCoordinateRing BaseRing⁄BaseRing] ≃ₗ[ordinaryCoordinateRing BaseRing]
      ordinaryCoordinateRing BaseRing) :=
  MazurTransfer.mixed_quadratic_coordinate_kaehler_equiv BaseRing _ _
    (MazurTransfer.order13_mixed_quadratic_unit_and_smoothness_certificates.1 BaseRing (dyadic_integer_unit 117 (by norm_num)))

theorem reciprocal_kaehler_equiv :
    Nonempty (Ω[reciprocalCoordinateRing BaseRing⁄BaseRing] ≃ₗ[reciprocalCoordinateRing BaseRing]
      reciprocalCoordinateRing BaseRing) :=
  MazurTransfer.mixed_quadratic_coordinate_kaehler_equiv BaseRing _ _
    (MazurTransfer.order13_mixed_quadratic_unit_and_smoothness_certificates.2.2.1 BaseRing (dyadic_integer_unit 39 (by norm_num)))

end MazurTransfer.Order13DyadicMixedQuadraticDifferentials
end
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual dyadic mixed quadratic charts and their whole
smooth proper curve are smooth of relative dimension exactly one.
Named downstream consumer: integral Picard representability at two.
-/
noncomputable section
namespace MazurTransfer.Order13DyadicMixedQuadraticRelativeDimension
open CategoryTheory AlgebraicGeometry
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticGluedCurve
open Order13DyadicMixedQuadraticChartDomains Order13DyadicMixedQuadraticDifferentials

theorem ordinaryToBase_smooth_relativeDimension_one :
    SmoothOfRelativeDimension 1 (ordinaryToBase BaseRing) := by
  letI : IsDomain (ordinaryCoordinateRing BaseRing) := ordinaryDyadic_isDomain
  letI : Algebra.Smooth BaseRing (ordinaryCoordinateRing BaseRing) := ordinary_algebra_smooth
  unfold ordinaryToBase ordinaryScheme
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  exact MazurTransfer.locally_standardSmooth_relativeDimension_one_of_kaehler_equiv BaseRing
    (ordinaryCoordinateRing BaseRing) ordinary_kaehler_equiv

theorem reciprocalToBase_smooth_relativeDimension_one :
    SmoothOfRelativeDimension 1 (reciprocalToBase BaseRing) := by
  letI : IsDomain (reciprocalCoordinateRing BaseRing) := reciprocalDyadic_isDomain
  letI : Algebra.Smooth BaseRing (reciprocalCoordinateRing BaseRing) := reciprocal_algebra_smooth
  unfold reciprocalToBase reciprocalScheme
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  exact MazurTransfer.locally_standardSmooth_relativeDimension_one_of_kaehler_equiv BaseRing
    (reciprocalCoordinateRing BaseRing) reciprocal_kaehler_equiv

theorem curveToBase_smooth_relativeDimension_one :
    SmoothOfRelativeDimension 1 (curveToBase BaseRing) := by
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension 1) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension 1)
      (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1))
  apply IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension 1)
    (f := curveToBase BaseRing) (glueData BaseRing).openCover
  intro i
  cases i
  · change SmoothOfRelativeDimension 1 (ordinaryChartMap BaseRing ≫ curveToBase BaseRing)
    rw [ordinaryChartMap_curveToBase]
    exact ordinaryToBase_smooth_relativeDimension_one
  · change SmoothOfRelativeDimension 1 (reciprocalChartMap BaseRing ≫ curveToBase BaseRing)
    rw [reciprocalChartMap_curveToBase]
    exact reciprocalToBase_smooth_relativeDimension_one

end MazurTransfer.Order13DyadicMixedQuadraticRelativeDimension
end
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual noetherian reduced base, proper relative curve of
dimension one, geometric integrality and a section over Z_(2).
Named downstream consumer: constructing the compatible dyadic Picard family;
its finite-map and chart-section representation inputs remain separate.
-/
noncomputable section
namespace MazurTransfer.Order13DyadicMixedQuadraticPicardGeometryInputs
open CategoryTheory AlgebraicGeometry
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticGluedCurve

theorem actual_dyadic_picard_geometry_inputs :
    IsNoetherianRing BaseRing ∧ IsReduced BaseRing ∧ IsProper (curveToBase BaseRing) ∧
      SmoothOfRelativeDimension 1 (curveToBase BaseRing) ∧
      GeometricallyIntegral (curveToBase BaseRing) ∧
      Nonempty (NeronModelInfra.SchemeHomOver (𝟙 (Spec (.of BaseRing))) (curveToBase BaseRing)) := by
  exact ⟨Order13DyadicMixedQuadraticChartDomains.base_isNoetherianRing, inferInstance,
    MazurTransfer.order13_actual_mixed_quadratic_curve_proper BaseRing,
    Order13DyadicMixedQuadraticRelativeDimension.curveToBase_smooth_relativeDimension_one,
    MazurTransfer.order13_actual_mixed_curve_geometricallyIntegral BaseRing, ⟨zeroSection⟩⟩

theorem actual_dyadic_curve_geometricallyConnected : GeometricallyConnected (curveToBase BaseRing) := by
  have hi := MazurTransfer.order13_actual_mixed_curve_geometricallyIntegral BaseRing
  constructor
  intro K _ y Z fst snd hp
  haveI : IsIntegral Z := hi.geometrically_isIntegral y fst snd hp
  infer_instance

end MazurTransfer.Order13DyadicMixedQuadraticPicardGeometryInputs
end
theorem solution : (SmoothOfRelativeDimension 1 (ordinaryToBase BaseRing)) ∧ (SmoothOfRelativeDimension 1 (reciprocalToBase BaseRing)) ∧ (SmoothOfRelativeDimension 1 (curveToBase BaseRing)) ∧ (IsNoetherianRing BaseRing ∧ IsReduced BaseRing ∧ IsProper (curveToBase BaseRing) ∧
      SmoothOfRelativeDimension 1 (curveToBase BaseRing) ∧
      GeometricallyIntegral (curveToBase BaseRing) ∧
      Nonempty (NeronModelInfra.SchemeHomOver (𝟙 (Spec (.of BaseRing))) (curveToBase BaseRing))) ∧ (GeometricallyConnected (curveToBase BaseRing)) := by
  exact ⟨MazurTransfer.Order13DyadicMixedQuadraticRelativeDimension.ordinaryToBase_smooth_relativeDimension_one,MazurTransfer.Order13DyadicMixedQuadraticRelativeDimension.reciprocalToBase_smooth_relativeDimension_one,MazurTransfer.Order13DyadicMixedQuadraticRelativeDimension.curveToBase_smooth_relativeDimension_one,MazurTransfer.Order13DyadicMixedQuadraticPicardGeometryInputs.actual_dyadic_picard_geometry_inputs,MazurTransfer.Order13DyadicMixedQuadraticPicardGeometryInputs.actual_dyadic_curve_geometricallyConnected⟩
#print axioms solution
