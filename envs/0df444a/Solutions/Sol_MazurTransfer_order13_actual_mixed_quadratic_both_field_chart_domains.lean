-- Prove2me | solution 1 for MazurTransfer.order13_actual_mixed_quadratic_both_field_chart_domains
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T05:24:48.896873+00:00
-- url     : https://prove2.me/submissions/d4c19b2b-ede7-44c5-b97f-5ab54cc74601

import Mathlib
import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalFiniteHyperellipticMapAndProperCurveDataDistinctProjectiveLineNamespaceV320261019
import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalWholeCurveBaseChangeData20261019
noncomputable section
open CategoryTheory AlgebraicGeometry MazurTransfer
open Order13MixedQuadraticGluedCurve
universe u
namespace MazurTransfer.MixedQuadraticFieldChartDomainOriginalProofHelpers20261019
end MazurTransfer.MixedQuadraticFieldChartDomainOriginalProofHelpers20261019
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a mixed monic quadratic cannot factor when its linear
coefficient has larger degree than its nonzero constant polynomial.
Named downstream consumer: ordinary chart integrality in every field,
including the characteristic-two geometric fibre of the dyadic family.
-/
noncomputable section
namespace MazurTransfer.MixedQuadraticFieldChartDomainOriginalProofHelpers20261019.Generic
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

end MazurTransfer.MixedQuadraticFieldChartDomainOriginalProofHelpers20261019.Generic
#print axioms MazurTransfer.MixedQuadraticFieldChartDomainOriginalProofHelpers20261019.Generic.irreducible_equation
#print axioms MazurTransfer.MixedQuadraticFieldChartDomainOriginalProofHelpers20261019.Generic.ordinary_field_isDomain

end
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: both actual mixed quadratic chart algebras are domains
over EVERY field, including characteristic two, with no smoothness premise.
Named downstream consumer: geometric integrality of the dyadic curve family.
-/
noncomputable section
namespace MazurTransfer.MixedQuadraticFieldChartDomainOriginalProofHelpers20261019.Charts
open Polynomial Module
open MixedQuadraticCoordinateJacobian MazurTransfer.MixedQuadraticFieldChartDomainOriginalProofHelpers20261019.Generic
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

end MazurTransfer.MixedQuadraticFieldChartDomainOriginalProofHelpers20261019.Charts
end
theorem solution : (∀ (K : Type u) [Field K], IsDomain (Order13DyadicMixedQuadraticCharts.ordinaryCoordinateRing K)) ∧ (∀ (K : Type u) [Field K], IsDomain (Order13DyadicMixedQuadraticCharts.reciprocalCoordinateRing K)) := by
  exact ⟨MazurTransfer.MixedQuadraticFieldChartDomainOriginalProofHelpers20261019.Generic.ordinary_field_isDomain,MazurTransfer.MixedQuadraticFieldChartDomainOriginalProofHelpers20261019.Charts.reciprocal_field_isDomain⟩
#print axioms solution
