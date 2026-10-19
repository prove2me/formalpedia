-- Prove2me | solution 1 for MazurTransfer.order13_actual_mixed_curve_geometricallyIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T05:06:33.281641+00:00
-- url     : https://prove2.me/submissions/cb2601f7-6e5e-44d6-b9dd-2f5c5c0d564e

import Mathlib
import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalFiniteHyperellipticMapAndProperCurveDataDistinctProjectiveLineNamespaceV320261019
import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalWholeCurveBaseChangeData20261019
import Theorems.Thm_MazurTransfer_integral_of_two_chart_gluing
noncomputable section
open CategoryTheory AlgebraicGeometry MazurTransfer
open Order13MixedQuadraticGluedCurve
universe u
namespace MazurTransfer.Order13MixedCurveGeometricIntegralityOriginalProofHelpers20261019
end MazurTransfer.Order13MixedCurveGeometricIntegralityOriginalProofHelpers20261019
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a mixed monic quadratic cannot factor when its linear
coefficient has larger degree than its nonzero constant polynomial.
Named downstream consumer: ordinary chart integrality in every field,
including the characteristic-two geometric fibre of the dyadic family.
-/
noncomputable section
namespace MazurTransfer.Order13MixedCurveGeometricIntegralityOriginalProofHelpers20261019.Generic
open Polynomial MixedQuadraticCoordinateJacobian
open Order13MixedQuadraticChartFiniteAlgebras Order13MixedQuadraticJacobianCertificates
open Order13DyadicMixedQuadraticCharts
variable (R : Type u) [CommRing R] [IsDomain R]

theorem equation_natDegree (h f : Polynomial R) : (equation R h f).natDegree = 2 := by
  unfold equation
  rw [natDegree_sub_C]
  calc
    _ = natDegree (X ^ 2 : Polynomial (Polynomial R)) := by
      apply natDegree_add_eq_left_of_natDegree_lt
      calc
        natDegree (C h * X : Polynomial (Polynomial R)) ≤ natDegree (C h) + natDegree X := natDegree_mul_le
        _ = 1 := by simp
        _ < natDegree (X ^ 2 : Polynomial (Polynomial R)) := by simp
    _ = 2 := by simp

theorem irreducible_equation (h f : Polynomial R) (hf : f ≠ 0) (hdeg : f.natDegree < h.natDegree) :
    Irreducible (equation R h f) := by
  by_contra hirr
  obtain ⟨a,b,hm,hs⟩ := ((mixed_equation_monic R h f).not_irreducible_iff_exists_add_mul_eq_coeff
    (equation_natDegree R h f)).mp hirr
  have hmul : a * b = -f := by simpa [equation] using hm.symm
  have hsum : a + b = h := by simpa [equation] using hs.symm
  have ha : a ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hmul
    exact hf (neg_eq_zero.mp hmul.symm)
  have hb : b ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hmul
    exact hf (neg_eq_zero.mp hmul.symm)
  have hnat := congrArg Polynomial.natDegree hmul
  rw [natDegree_mul ha hb, natDegree_neg] at hnat
  have hle : h.natDegree ≤ f.natDegree := by
    calc
      _ = (a+b).natDegree := congrArg Polynomial.natDegree hsum.symm
      _ ≤ max a.natDegree b.natDegree := natDegree_add_le _ _
      _ ≤ a.natDegree + b.natDegree := max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
      _ = _ := hnat
  exact (not_lt_of_ge hle) hdeg

theorem ordinaryH_natDegree : (ordinaryH R).natDegree = 3 := by
  change (X ^ 3 + X ^ 2 + C (1 : R)).natDegree = 3
  rw [natDegree_add_C]
  rw [natDegree_add_eq_left_of_natDegree_lt (by simp : natDegree (X^2 : Polynomial R) < natDegree (X^3 : Polynomial R))]
  simp

theorem ordinaryF_natDegree : (ordinaryF R).natDegree = 2 := by
  change (X * (X + C (1 : R))).natDegree = 2
  rw [natDegree_mul X_ne_zero (X_add_C_ne_zero 1)]
  rw [natDegree_X, natDegree_X_add_C]

theorem ordinary_equation_irreducible : Irreducible (ordinaryEquation R) := by
  apply irreducible_equation
  · intro hz
    have ht := ordinaryF_natDegree R
    rw [hz, natDegree_zero] at ht
    norm_num at ht
  · rw [ordinaryF_natDegree, ordinaryH_natDegree]
    decide

theorem ordinary_field_isDomain (K : Type u) [Field K] : IsDomain (ordinaryCoordinateRing K) :=
  AdjoinRoot.isDomain_of_prime (irreducible_iff_prime.mp (ordinary_equation_irreducible K))

end MazurTransfer.Order13MixedCurveGeometricIntegralityOriginalProofHelpers20261019.Generic
#print axioms MazurTransfer.Order13MixedCurveGeometricIntegralityOriginalProofHelpers20261019.Generic.irreducible_equation
#print axioms MazurTransfer.Order13MixedCurveGeometricIntegralityOriginalProofHelpers20261019.Generic.ordinary_field_isDomain

end
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: both actual mixed quadratic chart algebras are domains
over EVERY field, including characteristic two, with no smoothness premise.
Named downstream consumer: geometric integrality of the dyadic curve family.
-/
noncomputable section
namespace MazurTransfer.Order13MixedCurveGeometricIntegralityOriginalProofHelpers20261019.Charts
open Polynomial Module
open MixedQuadraticCoordinateJacobian MazurTransfer.Order13MixedCurveGeometricIntegralityOriginalProofHelpers20261019.Generic
open Order13MixedQuadraticChartFiniteAlgebras Order13MixedQuadraticJacobianCertificates
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedQuadraticOverlapEquivalence
variable (K : Type u) [Field K]

theorem ordinary_x_ne_zero : xCoordinate K ≠ 0 := by
  have hd : (ordinaryEquation K).degree ≠ 0 := by
    rw [degree_eq_natDegree (ordinaryEquation_monic K).ne_zero, equation_natDegree K]
    norm_num
  have hi := AdjoinRoot.of.injective_of_degree_ne_zero hd
  intro hz
  apply X_ne_zero (R := K)
  exact hi (hz.trans (map_zero (AdjoinRoot.of (ordinaryEquation K))).symm)

theorem ordinaryOverlap_isDomain : IsDomain (OrdinaryOverlapRing K) := by
  letI := ordinary_field_isDomain K
  exact Localization.Away.isDomain (ordinary_x_ne_zero K)

theorem reciprocal_z_regular : IsRegular (zCoordinate K) := by
  letI : Module.Free (Polynomial K) (reciprocalCoordinateRing K) := (reciprocalEquation_monic K).free_adjoinRoot
  have hm : IsSMulRegular (reciprocalCoordinateRing K) (X : Polynomial K) :=
    Module.IsTorsionFree.isSMulRegular (isRegular_iff_ne_zero.mpr X_ne_zero)
  have hl : IsLeftRegular (zCoordinate K) := by
    intro a b hab
    apply hm
    simp only [Algebra.smul_def, AdjoinRoot.algebraMap_eq]
    exact hab
  refine ⟨hl, ?_⟩
  intro a b hab
  apply hl
  simpa only [mul_comm] using hab

theorem reciprocal_localization_injective : Function.Injective
    (algebraMap (reciprocalCoordinateRing K) (ReciprocalOverlapRing K)) := by
  apply IsLocalization.injectiveₛ (M := Submonoid.powers (zCoordinate K))
  intro r hr
  obtain ⟨n,rfl⟩ := hr
  exact (reciprocal_z_regular K).pow n

theorem reciprocalOverlap_isDomain : IsDomain (ReciprocalOverlapRing K) := by
  letI := ordinaryOverlap_isDomain K
  exact MulEquiv.isDomain _ (overlapAlgEquiv K).symm.toRingEquiv.toMulEquiv

theorem reciprocal_field_isDomain : IsDomain (reciprocalCoordinateRing K) := by
  letI := reciprocalOverlap_isDomain K
  exact Function.Injective.isDomain
    (algebraMap (reciprocalCoordinateRing K) (ReciprocalOverlapRing K)) (reciprocal_localization_injective K)

end MazurTransfer.Order13MixedCurveGeometricIntegralityOriginalProofHelpers20261019.Charts
#print axioms MazurTransfer.Order13MixedCurveGeometricIntegralityOriginalProofHelpers20261019.Charts.ordinaryOverlap_isDomain
#print axioms MazurTransfer.Order13MixedCurveGeometricIntegralityOriginalProofHelpers20261019.Charts.reciprocal_field_isDomain

end
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Adapts the complete checked two-chart integrality argument of the original
order-thirteen model, using its integral_of_two_chart_gluing theorem.
Design boundary: the ACTUAL mixed quadratic glued curve is integral over
every field, including characteristic two. Named downstream consumer:
geometric integrality of the whole dyadic family for Picard construction.
-/
noncomputable section
namespace MazurTransfer.Order13MixedCurveGeometricIntegralityOriginalProofHelpers20261019.Whole
open CategoryTheory AlgebraicGeometry
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticGluedCurve
open Order13MixedQuadraticOverlapCoordinates MazurTransfer.Order13MixedCurveGeometricIntegralityOriginalProofHelpers20261019.Charts
variable (K : Type u) [Field K]

theorem curveScheme_isIntegral : IsIntegral (curveScheme K) := by
  letI : IsDomain (ordinaryCoordinateRing K) := MazurTransfer.Order13MixedCurveGeometricIntegralityOriginalProofHelpers20261019.Generic.ordinary_field_isDomain K
  letI : IsDomain (reciprocalCoordinateRing K) := reciprocal_field_isDomain K
  haveI : IsIntegral ((glueData K).U Chart.ordinary) := by
    change IsIntegral (ordinaryScheme K)
    unfold ordinaryScheme
    exact (affine_isIntegral_iff (.of (ordinaryCoordinateRing K))).mpr inferInstance
  haveI : IsIntegral ((glueData K).U Chart.reciprocal) := by
    change IsIntegral (reciprocalScheme K)
    unfold reciprocalScheme
    exact (affine_isIntegral_iff (.of (reciprocalCoordinateRing K))).mpr inferInstance
  have hv : (glueData K).V (Chart.ordinary, Chart.reciprocal) =
      Spec (.of (OrdinaryOverlapRing K)) := by
    dsimp only [glueData, categoricalGlueData, CategoryTheory.GlueData.ofGlueData']
    exact dif_neg (by intro h; cases h)
  apply MazurTransfer.integral_of_two_chart_gluing (glueData K) Chart.ordinary Chart.reciprocal
  · intro i
    cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rw [hv]
    letI := ordinaryOverlap_isDomain K
    infer_instance

end MazurTransfer.Order13MixedCurveGeometricIntegralityOriginalProofHelpers20261019.Whole
#print axioms MazurTransfer.Order13MixedCurveGeometricIntegralityOriginalProofHelpers20261019.Whole.curveScheme_isIntegral

end
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: geometric integrality of the actual mixed quadratic curve
over EVERY commutative coefficient ring, using the genuine whole base-change
square and the independently proved integral model over every field.
Named downstream consumer: dyadic integral Picard representability.
-/
noncomputable section
namespace MazurTransfer.Order13MixedCurveGeometricIntegralityOriginalProofHelpers20261019.Geometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Order13MixedQuadraticGluedCurve
open MazurTransfer.Order13MixedQuadraticActualCurveBaseChange

theorem curveToBase_geometricallyIntegral (R : Type u) [CommRing R]
    : GeometricallyIntegral (curveToBase R) := by
  constructor
  intro K _ y Z fst snd hp
  let f : R →+* K := (Spec.preimage y).hom
  letI : Algebra R K := f.toAlgebra
  have hy : Spec.map (CommRingCat.ofHom (algebraMap R K)) = y := by
    exact Spec.map_preimage y
  letI : IsIntegral (curveScheme K) := MazurTransfer.Order13MixedCurveGeometricIntegralityOriginalProofHelpers20261019.Whole.curveScheme_isIntegral K
  have hcurve : IsPullback (curveMap R K) (curveToBase K) (curveToBase R) y := by
    rw [← hy]
    exact wholeCurve_isPullback R K
  let e : Z ≅ curveScheme K := hp.isoPullback ≪≫ hcurve.isoPullback.symm
  exact IsIntegral.of_isIso e.inv

end MazurTransfer.Order13MixedCurveGeometricIntegralityOriginalProofHelpers20261019.Geometry
#print axioms MazurTransfer.Order13MixedCurveGeometricIntegralityOriginalProofHelpers20261019.Geometry.curveToBase_geometricallyIntegral

end
theorem solution : ∀ (R : Type u) [CommRing R], GeometricallyIntegral (curveToBase R) := by
  exact MazurTransfer.Order13MixedCurveGeometricIntegralityOriginalProofHelpers20261019.Geometry.curveToBase_geometricallyIntegral
#print axioms solution
