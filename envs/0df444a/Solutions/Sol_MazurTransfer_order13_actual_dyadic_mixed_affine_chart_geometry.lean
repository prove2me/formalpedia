-- Prove2me | solution 1 for MazurTransfer.order13_actual_dyadic_mixed_affine_chart_geometry
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T02:28:01.749449+00:00
-- url     : https://prove2.me/submissions/29ccf142-b005-486f-ad44-876a2d111bfe

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual ordinary and reciprocal affine mixed quadratic
schemes over Z localized at two, both smooth, flat and locally finitely
presented. Named downstream consumer: their gluing and comparison with
the existing rational order-thirteen curve. Proper gluing is separate.
-/
import Definitions.Def_MazurTransfer_Order13DyadicMixedOriginalAffineChartData20261019
import Theorems.Thm_MazurTransfer_order13_mixed_quadratic_unit_and_smoothness_certificates
noncomputable section
open CategoryTheory AlgebraicGeometry MazurTransfer.Order13LocalIntegralCoefficientMaps MazurTransfer.Order13DyadicMixedQuadraticCharts
attribute [local instance] dyadicChartOriginalPrimeTwoProvider20261019
namespace MazurTransfer.Order13ActualDyadicAffineChartGeometryProofHelpers20261019
theorem dyadic_integer_unit (n : ℕ) (hn : ¬ (2 : ℤ) ∣ (n : ℤ)) :
    IsUnit (n : BaseRing) := by
  have h : (n : ℤ) ∈ (primeIdeal 2).primeCompl := by
    change (n : ℤ) ∉ Ideal.span {(2 : ℤ)}
    rw [Ideal.mem_span_singleton]
    exact hn
  simpa only [_root_.map_natCast] using IsLocalization.map_units BaseRing ⟨(n : ℤ), h⟩

theorem ordinary_algebra_smooth : Algebra.Smooth BaseRing (ordinaryCoordinateRing BaseRing) :=
  (MazurTransfer.order13_mixed_quadratic_unit_and_smoothness_certificates).2.1 BaseRing (dyadic_integer_unit 117 (by norm_num))
theorem reciprocal_algebra_smooth : Algebra.Smooth BaseRing (reciprocalCoordinateRing BaseRing) :=
  (MazurTransfer.order13_mixed_quadratic_unit_and_smoothness_certificates).2.2.2 BaseRing (dyadic_integer_unit 39 (by norm_num))

theorem ordinaryToBase_smooth : Smooth (ordinaryToBase BaseRing) := by
  unfold ordinaryToBase ordinaryScheme
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.mpr ordinary_algebra_smooth

theorem reciprocalToBase_smooth : Smooth (reciprocalToBase BaseRing) := by
  unfold reciprocalToBase reciprocalScheme
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.mpr reciprocal_algebra_smooth

theorem actual_dyadic_affine_chart_geometry :
    (Smooth (ordinaryToBase BaseRing) ∧ Flat (ordinaryToBase BaseRing) ∧
      LocallyOfFinitePresentation (ordinaryToBase BaseRing)) ∧
    (Smooth (reciprocalToBase BaseRing) ∧ Flat (reciprocalToBase BaseRing) ∧
      LocallyOfFinitePresentation (reciprocalToBase BaseRing)) := by
  letI : Smooth (ordinaryToBase BaseRing) := ordinaryToBase_smooth
  letI : Smooth (reciprocalToBase BaseRing) := reciprocalToBase_smooth
  exact ⟨⟨inferInstance, inferInstance, inferInstance⟩,
    ⟨inferInstance, inferInstance, inferInstance⟩⟩

end MazurTransfer.Order13ActualDyadicAffineChartGeometryProofHelpers20261019
theorem solution :
    (Smooth (ordinaryToBase BaseRing) ∧ Flat (ordinaryToBase BaseRing) ∧
      LocallyOfFinitePresentation (ordinaryToBase BaseRing)) ∧
    (Smooth (reciprocalToBase BaseRing) ∧ Flat (reciprocalToBase BaseRing) ∧
      LocallyOfFinitePresentation (reciprocalToBase BaseRing)) := by
  exact MazurTransfer.Order13ActualDyadicAffineChartGeometryProofHelpers20261019.actual_dyadic_affine_chart_geometry
#print axioms solution
