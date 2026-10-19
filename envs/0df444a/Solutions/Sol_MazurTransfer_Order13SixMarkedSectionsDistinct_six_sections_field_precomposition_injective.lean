-- Prove2me | solution 1 for MazurTransfer.Order13SixMarkedSectionsDistinct.six_sections_field_precomposition_injective
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T04:41:19.995228+00:00
-- url     : https://prove2.me/submissions/da68a178-fd60-4dfd-bb9e-8f5f477c6e8d

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Design boundary: unchanged six actual marked sections remain distinct after precomposition with any field point when two is a unit.
Named downstream consumer: actual integral Picard chart sections.
Original per-file attribution and checked proof bodies are retained below. -/
import Definitions.Def_MazurTransfer_Order13SixMarkedIntegralSections
noncomputable section
universe u
namespace SixMarkedSectionsDistinctPublicProof20261017
namespace MazurTransfer.Order13IntegralHyperellipticMap
open CategoryTheory AlgebraicGeometry Polynomial
open _root_.MazurTorsion
variable (K : Type u) [CommRing K]
private theorem ordinary_ne_reciprocal :
    (XOneThirteenProjectiveCurve.Chart.ordinary :
      XOneThirteenProjectiveCurve.Chart.{u}) ≠
      XOneThirteenProjectiveCurve.Chart.reciprocal := by
  intro h
  cases h
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Copyright (c) 2026 Vas and contributors.
Released under Apache-2.0. Authors: Vasily Ilin.
Complete gluing, preimage, finite-morphism and properness proofs adapted
from the pinned WIP-compatible XOneThirteenHyperellipticMap.lean.
The coefficient ring is an arbitrary commutative ring, with no field or
characteristic restriction. No Noetherianity conclusion is asserted for
an arbitrary base ring. The independent adaptation uses the campaign
Mathlib pin and does not alter the core or separate Tau Ceti package pins.
Design boundary: the actual whole integral hyperelliptic map is finite,
and the literal glued order-thirteen curve is proper over its base ring.
Named downstream consumer: the actual smooth proper integral curve family
and its compatible Picard family for torsion specialization.
-/
private theorem reciprocal_ne_ordinary :
    (XOneThirteenProjectiveCurve.Chart.reciprocal :
      XOneThirteenProjectiveCurve.Chart.{u}) ≠
      XOneThirteenProjectiveCurve.Chart.ordinary := by
  intro h
  cases h

private theorem reciprocalOrdinaryOverlapInclusion_eq :
    XOneThirteenProjectiveCurve.overlapInclusion K
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u}) reciprocal_ne_ordinary =
      Spec.map (CommRingCat.ofHom
        (algebraMap (XOneThirteenProjectiveCurve.ReciprocalRing K)
          (XOneThirteenProjectiveCurve.ReciprocalOverlapRing K))) := by
  rfl

private instance reciprocalOverlapInclusion_isOpenImmersion :
    IsOpenImmersion
      (XOneThirteenProjectiveCurve.overlapInclusion K
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})
        reciprocal_ne_ordinary) := by
  rw [reciprocalOrdinaryOverlapInclusion_eq]
  exact IsOpenImmersion.of_isLocalization
    (XOneThirteenProjectiveCurve.zCoordinate K)

private noncomputable abbrev reciprocalOverlapOpen :
    (XOneThirteenProjectiveCurve.chartScheme K
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})).Opens :=
  PrimeSpectrum.basicOpen (XOneThirteenProjectiveCurve.zCoordinate K)

private theorem reciprocalOverlapInclusion_opensRange :
    (XOneThirteenProjectiveCurve.overlapInclusion K
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})
      (XOneThirteenProjectiveCurve.Chart.ordinary :
        XOneThirteenProjectiveCurve.Chart.{u})
      reciprocal_ne_ordinary).opensRange =
        reciprocalOverlapOpen K := by
  rw [SetLike.ext'_iff]
  exact PrimeSpectrum.localization_away_comap_range
    (XOneThirteenProjectiveCurve.ReciprocalOverlapRing K)
    (XOneThirteenProjectiveCurve.zCoordinate K)

private instance reciprocalGlueOverlap_isOpenImmersion :
    IsOpenImmersion
      ((XOneThirteenProjectiveCurve.glueData K).f
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})) :=
  (XOneThirteenProjectiveCurve.glueData K).f_open _ _

private theorem reciprocalGlueOverlap_opensRange :
    ((XOneThirteenProjectiveCurve.glueData K).f
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})
      (XOneThirteenProjectiveCurve.Chart.ordinary :
        XOneThirteenProjectiveCurve.Chart.{u})).opensRange =
      reciprocalOverlapOpen K := by
  dsimp [XOneThirteenProjectiveCurve.glueData,
    XOneThirteenProjectiveCurve.categoricalGlueData,
    CategoryTheory.GlueData.ofGlueData',
    CategoryTheory.GlueData'.f',
    ordinary_ne_reciprocal, reciprocal_ne_ordinary]
  simp only [dif_neg reciprocal_ne_ordinary]
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact reciprocalOverlapInclusion_opensRange K

private theorem reciprocalChartMap_preimage_ordinaryChartMap_opensRange :
    XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
        (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange =
      ((XOneThirteenProjectiveCurve.glueData K).f
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})).opensRange := by
  apply TopologicalSpace.Opens.ext
  ext q
  change (XOneThirteenProjectiveCurve.reciprocalChartMap K q ∈
      (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange) ↔
    q ∈ ((XOneThirteenProjectiveCurve.glueData K).f
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})
      (XOneThirteenProjectiveCurve.Chart.ordinary :
        XOneThirteenProjectiveCurve.Chart.{u})).opensRange
  constructor
  · rintro ⟨r, hr⟩
    have hrel :=
      ((XOneThirteenProjectiveCurve.glueData K).ι_eq_iff
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u}) q r).mp hr.symm
    obtain ⟨x, hx, -⟩ := hrel
    exact ⟨x, hx⟩
  · rintro ⟨x, rfl⟩
    refine ⟨((XOneThirteenProjectiveCurve.glueData K).t
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u}) ≫
        (XOneThirteenProjectiveCurve.glueData K).f
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u})) x, ?_⟩
    exact congrArg (fun f ↦ f x)
      ((XOneThirteenProjectiveCurve.glueData K).glue_condition
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u}))

private theorem reciprocalOverlapOpen_eq_chartMap_preimage :
    reciprocalOverlapOpen K =
      XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
        (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange :=
  (reciprocalGlueOverlap_opensRange K).symm.trans
    (reciprocalChartMap_preimage_ordinaryChartMap_opensRange K).symm

/-- On the reciprocal chart, the overlap with the ordinary chart is exactly
the principal open where the reciprocal coordinate `z` is nonzero. -/
@[simp]
theorem reciprocalChartMap_preimage_ordinaryChartMap_opensRange_eq_basicOpen :
    XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
        (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange =
      PrimeSpectrum.basicOpen
        (XOneThirteenProjectiveCurve.zCoordinate K) := by
  exact (reciprocalOverlapOpen_eq_chartMap_preimage K).symm

end MazurTransfer.Order13IntegralHyperellipticMap

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: consume the retained exact chart-overlap proof as a set
range identity. Named downstream consumer: the actual positive infinity
complement in the whole two-chart curve. No affine identification is assumed.
Complete owned overlap proof retained in Order13IntegralCurveProperViaHyperellipticMap,
source SHA256 d0824f30d9fdce54da798e955c01eb49d50aacbaaaaa095490fa7585b4466856.
-/


noncomputable section
namespace MazurTransfer.Order13ActualTwoChartRangeOverlap
open CategoryTheory AlgebraicGeometry
open MazurTorsion.XOneThirteenProjectiveCurve
variable (R : Type u) [CommRing R]

theorem reciprocalChartMap_preimage_ordinary_range :
    reciprocalChartMap R ⁻¹' Set.range (ordinaryChartMap R) =
      (PrimeSpectrum.basicOpen (zCoordinate R) : Set (PrimeSpectrum (ReciprocalRing R))) := by
  exact congrArg (fun U : (reciprocalScheme R).Opens => (U : Set (reciprocalScheme R)))
    (Order13IntegralHyperellipticMap.reciprocalChartMap_preimage_ordinaryChartMap_opensRange_eq_basicOpen R)

end MazurTransfer.Order13ActualTwoChartRangeOverlap


end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: literal evaluation coordinates distinguish section images
above every prime of the coefficient ring; infinity images avoid the ordinary
chart. Named downstream consumer: fibrewise distinctness of the six marked
integral sections in the original Picard chart-section criterion.
-/


noncomputable section
namespace MazurTransfer.Order13MarkedSectionPointSeparation
open CategoryTheory AlgebraicGeometry Polynomial
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open _root_.MazurTransfer.Order13IntegralSections
open InverseParameterChartComparisonLibrary.MazurTransfer.Order13IntegralSections (reciprocalInfinityEvaluation_z reciprocalInfinityEvaluation_w)
variable (R : Type u) [CommRing R]

theorem ordinaryEvaluation_coefficient (t a : R)
    (ha : a^2 = (sexticPolynomial R).eval t) (r : R) :
    ordinaryEvaluation R t a ha (algebraMap R (CoordinateRing R) r) = r :=
  RingHom.congr_fun (ordinaryEvaluation_comp_algebraMap R t a ha) r

theorem infinityEvaluation_coefficient (a : R) (ha : a^2=1) (r : R) :
    reciprocalInfinityEvaluation R a ha (algebraMap R (ReciprocalRing R) r) = r :=
  RingHom.congr_fun (reciprocalInfinityEvaluation_comp_algebraMap R a ha) r

theorem ordinary_point_equality_constants (p : PrimeSpectrum R) (t a u b : R)
    (ha : a^2 = (sexticPolynomial R).eval t)
    (hb : b^2 = (sexticPolynomial R).eval u)
    (h : ordinaryMorphism R t a ha p = ordinaryMorphism R u b hb p) :
    u-t ∈ p.asIdeal ∧ b-a ∈ p.asIdeal := by
  have hp := (ordinaryChartMap R).isOpenEmbedding.injective h
  change PrimeSpectrum.comap (ordinaryEvaluation R t a ha) p =
    PrimeSpectrum.comap (ordinaryEvaluation R u b hb) p at hp
  have hx : xCoordinate R - algebraMap R (CoordinateRing R) t ∈
      (PrimeSpectrum.comap (ordinaryEvaluation R t a ha) p).asIdeal := by
    change ordinaryEvaluation R t a ha _ ∈ p.asIdeal
    simp only [map_sub, ordinaryEvaluation_x, ordinaryEvaluation_coefficient, sub_self, Ideal.zero_mem]
  have hy : yCoordinate R - algebraMap R (CoordinateRing R) a ∈
      (PrimeSpectrum.comap (ordinaryEvaluation R t a ha) p).asIdeal := by
    change ordinaryEvaluation R t a ha _ ∈ p.asIdeal
    simp only [map_sub, ordinaryEvaluation_y, ordinaryEvaluation_coefficient, sub_self, Ideal.zero_mem]
  rw [hp] at hx hy
  change ordinaryEvaluation R u b hb _ ∈ p.asIdeal at hx hy
  simp only [map_sub, ordinaryEvaluation_x, ordinaryEvaluation_y, ordinaryEvaluation_coefficient] at hx hy
  exact ⟨hx,hy⟩

theorem infinity_point_equality_constants (p : PrimeSpectrum R) (a b : R)
    (ha : a^2=1) (hb : b^2=1)
    (h : infinityMorphism R a ha p = infinityMorphism R b hb p) : b-a ∈ p.asIdeal := by
  have hp := (reciprocalChartMap R).isOpenEmbedding.injective h
  change PrimeSpectrum.comap (reciprocalInfinityEvaluation R a ha) p =
    PrimeSpectrum.comap (reciprocalInfinityEvaluation R b hb) p at hp
  have hw : wCoordinate R - algebraMap R (ReciprocalRing R) a ∈
      (PrimeSpectrum.comap (reciprocalInfinityEvaluation R a ha) p).asIdeal := by
    change reciprocalInfinityEvaluation R a ha _ ∈ p.asIdeal
    simp only [map_sub, reciprocalInfinityEvaluation_w, infinityEvaluation_coefficient,
      sub_self, Ideal.zero_mem]
  rw [hp] at hw
  change reciprocalInfinityEvaluation R b hb _ ∈ p.asIdeal at hw
  simpa only [map_sub, reciprocalInfinityEvaluation_w, infinityEvaluation_coefficient] using hw

theorem infinity_point_not_ordinary (p : PrimeSpectrum R) (a : R) (ha : a^2=1) :
    infinityMorphism R a ha p ∉ Set.range (ordinaryChartMap R) := by
  intro h
  have hz := Set.ext_iff.mp
    (Order13ActualTwoChartRangeOverlap.reciprocalChartMap_preimage_ordinary_range R)
    ((Spec.map (CommRingCat.ofHom (reciprocalInfinityEvaluation R a ha))) p)
  have hn := hz.mp h
  change reciprocalInfinityEvaluation R a ha (zCoordinate R) ∉ p.asIdeal at hn
  rw [reciprocalInfinityEvaluation_z] at hn
  exact hn p.asIdeal.zero_mem

theorem infinity_ordinary_point_ne (p : PrimeSpectrum R) (a t b : R)
    (ha : a^2=1) (hb : b^2=(sexticPolynomial R).eval t) :
    infinityMorphism R a ha p ≠ ordinaryMorphism R t b hb p := by
  intro h
  apply infinity_point_not_ordinary R p a ha
  rw [h]
  exact ⟨(Spec.map (CommRingCat.ofHom (ordinaryEvaluation R t b hb))) p,rfl⟩

end MazurTransfer.Order13MarkedSectionPointSeparation




end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: point images of the six actual marked sections are distinct
above every prime when 2 is invertible; precomposition with a field point
therefore preserves distinctness as scheme morphisms.
Named downstream consumer: SixSectionPicardChartCriterion for the integral
order-13 curve family.
-/


noncomputable section
namespace MazurTransfer.Order13SixMarkedSectionsDistinct
open CategoryTheory AlgebraicGeometry Polynomial
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open _root_.MazurTransfer.Order13IntegralSections
open Order13MarkedSectionPointSeparation
variable (R : Type u) [CommRing R]

private theorem point_ne_0_1 (h2 : IsUnit (2 : R)) (p : PrimeSpectrum R) :
    (sixMarkedSections R 0).val p ≠ (sixMarkedSections R 1).val p := by
  intro h
  have he := infinity_point_equality_constants R p 1 (-1) (by simp) (by simp) h
  have hn : (-2 : R) ∉ p.asIdeal := Ideal.notMem_of_isUnit _ h2.neg
  apply hn
  convert he using 1; ring

private theorem point_ne_0_2 (_h2 : IsUnit (2 : R)) (p : PrimeSpectrum R) :
    (sixMarkedSections R 0).val p ≠ (sixMarkedSections R 2).val p := by
  exact infinity_ordinary_point_ne R p _ _ _ _ _

private theorem point_ne_0_3 (_h2 : IsUnit (2 : R)) (p : PrimeSpectrum R) :
    (sixMarkedSections R 0).val p ≠ (sixMarkedSections R 3).val p := by
  exact infinity_ordinary_point_ne R p _ _ _ _ _

private theorem point_ne_0_4 (_h2 : IsUnit (2 : R)) (p : PrimeSpectrum R) :
    (sixMarkedSections R 0).val p ≠ (sixMarkedSections R 4).val p := by
  exact infinity_ordinary_point_ne R p _ _ _ _ _

private theorem point_ne_0_5 (_h2 : IsUnit (2 : R)) (p : PrimeSpectrum R) :
    (sixMarkedSections R 0).val p ≠ (sixMarkedSections R 5).val p := by
  exact infinity_ordinary_point_ne R p _ _ _ _ _

private theorem point_ne_1_2 (_h2 : IsUnit (2 : R)) (p : PrimeSpectrum R) :
    (sixMarkedSections R 1).val p ≠ (sixMarkedSections R 2).val p := by
  exact infinity_ordinary_point_ne R p _ _ _ _ _

private theorem point_ne_1_3 (_h2 : IsUnit (2 : R)) (p : PrimeSpectrum R) :
    (sixMarkedSections R 1).val p ≠ (sixMarkedSections R 3).val p := by
  exact infinity_ordinary_point_ne R p _ _ _ _ _

private theorem point_ne_1_4 (_h2 : IsUnit (2 : R)) (p : PrimeSpectrum R) :
    (sixMarkedSections R 1).val p ≠ (sixMarkedSections R 4).val p := by
  exact infinity_ordinary_point_ne R p _ _ _ _ _

private theorem point_ne_1_5 (_h2 : IsUnit (2 : R)) (p : PrimeSpectrum R) :
    (sixMarkedSections R 1).val p ≠ (sixMarkedSections R 5).val p := by
  exact infinity_ordinary_point_ne R p _ _ _ _ _

private theorem point_ne_2_3 (h2 : IsUnit (2 : R)) (p : PrimeSpectrum R) :
    (sixMarkedSections R 2).val p ≠ (sixMarkedSections R 3).val p := by
  intro h
  have he := ordinary_point_equality_constants R p (0) (1) (0) (-1) _ _ h
  have hn : (-2 : R) ∉ p.asIdeal := Ideal.notMem_of_isUnit _ h2.neg
  apply hn
  convert he.2 using 1; ring

private theorem point_ne_2_4 (_h2 : IsUnit (2 : R)) (p : PrimeSpectrum R) :
    (sixMarkedSections R 2).val p ≠ (sixMarkedSections R 4).val p := by
  intro h
  have he := ordinary_point_equality_constants R p (0) (1) (-1) (1) _ _ h
  have hn : (-1 : R) ∉ p.asIdeal := Ideal.notMem_of_isUnit _ isUnit_one.neg
  apply hn
  convert he.1 using 1; ring

private theorem point_ne_2_5 (_h2 : IsUnit (2 : R)) (p : PrimeSpectrum R) :
    (sixMarkedSections R 2).val p ≠ (sixMarkedSections R 5).val p := by
  intro h
  have he := ordinary_point_equality_constants R p (0) (1) (-1) (-1) _ _ h
  have hn : (-1 : R) ∉ p.asIdeal := Ideal.notMem_of_isUnit _ isUnit_one.neg
  apply hn
  convert he.1 using 1; ring

private theorem point_ne_3_4 (_h2 : IsUnit (2 : R)) (p : PrimeSpectrum R) :
    (sixMarkedSections R 3).val p ≠ (sixMarkedSections R 4).val p := by
  intro h
  have he := ordinary_point_equality_constants R p (0) (-1) (-1) (1) _ _ h
  have hn : (-1 : R) ∉ p.asIdeal := Ideal.notMem_of_isUnit _ isUnit_one.neg
  apply hn
  convert he.1 using 1; ring

private theorem point_ne_3_5 (_h2 : IsUnit (2 : R)) (p : PrimeSpectrum R) :
    (sixMarkedSections R 3).val p ≠ (sixMarkedSections R 5).val p := by
  intro h
  have he := ordinary_point_equality_constants R p (0) (-1) (-1) (-1) _ _ h
  have hn : (-1 : R) ∉ p.asIdeal := Ideal.notMem_of_isUnit _ isUnit_one.neg
  apply hn
  convert he.1 using 1; ring

private theorem point_ne_4_5 (h2 : IsUnit (2 : R)) (p : PrimeSpectrum R) :
    (sixMarkedSections R 4).val p ≠ (sixMarkedSections R 5).val p := by
  intro h
  have he := ordinary_point_equality_constants R p (-1) (1) (-1) (-1) _ _ h
  have hn : (-2 : R) ∉ p.asIdeal := Ideal.notMem_of_isUnit _ h2.neg
  apply hn
  convert he.2 using 1; ring

theorem six_point_images_injective (h2 : IsUnit (2 : R)) (p : PrimeSpectrum R) :
    Function.Injective (fun i : Fin 6 => (sixMarkedSections R i).val p) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exact False.elim (point_ne_0_1 R h2 p hij)
  · exact False.elim (point_ne_0_2 R h2 p hij)
  · exact False.elim (point_ne_0_3 R h2 p hij)
  · exact False.elim (point_ne_0_4 R h2 p hij)
  · exact False.elim (point_ne_0_5 R h2 p hij)
  · exact False.elim (point_ne_0_1 R h2 p hij.symm)
  · rfl
  · exact False.elim (point_ne_1_2 R h2 p hij)
  · exact False.elim (point_ne_1_3 R h2 p hij)
  · exact False.elim (point_ne_1_4 R h2 p hij)
  · exact False.elim (point_ne_1_5 R h2 p hij)
  · exact False.elim (point_ne_0_2 R h2 p hij.symm)
  · exact False.elim (point_ne_1_2 R h2 p hij.symm)
  · rfl
  · exact False.elim (point_ne_2_3 R h2 p hij)
  · exact False.elim (point_ne_2_4 R h2 p hij)
  · exact False.elim (point_ne_2_5 R h2 p hij)
  · exact False.elim (point_ne_0_3 R h2 p hij.symm)
  · exact False.elim (point_ne_1_3 R h2 p hij.symm)
  · exact False.elim (point_ne_2_3 R h2 p hij.symm)
  · rfl
  · exact False.elim (point_ne_3_4 R h2 p hij)
  · exact False.elim (point_ne_3_5 R h2 p hij)
  · exact False.elim (point_ne_0_4 R h2 p hij.symm)
  · exact False.elim (point_ne_1_4 R h2 p hij.symm)
  · exact False.elim (point_ne_2_4 R h2 p hij.symm)
  · exact False.elim (point_ne_3_4 R h2 p hij.symm)
  · rfl
  · exact False.elim (point_ne_4_5 R h2 p hij)
  · exact False.elim (point_ne_0_5 R h2 p hij.symm)
  · exact False.elim (point_ne_1_5 R h2 p hij.symm)
  · exact False.elim (point_ne_2_5 R h2 p hij.symm)
  · exact False.elim (point_ne_3_5 R h2 p hij.symm)
  · exact False.elim (point_ne_4_5 R h2 p hij.symm)
  · rfl

theorem six_sections_field_precomposition_injective (h2 : IsUnit (2 : R))
    (k : Type u) [Field k] (s : Spec (.of k) ⟶ Spec (.of R)) :
    Function.Injective (fun i : Fin 6 => s ≫ (sixMarkedSections R i).val) := by
  intro i j hij
  have hp := congrArg
    (fun f : Spec (.of k) ⟶ curveScheme R => f (IsLocalRing.closedPoint k)) hij
  exact six_point_images_injective R h2 (s (IsLocalRing.closedPoint k)) hp

end MazurTransfer.Order13SixMarkedSectionsDistinct




end
end SixMarkedSectionsDistinctPublicProof20261017
open CategoryTheory AlgebraicGeometry
open MazurTorsion.XOneThirteenProjectiveCurve MazurTransfer.Order13IntegralSections
theorem solution (R : Type u) [CommRing R] (h2 : IsUnit (2 : R)) (k : Type u) [Field k] (s : Spec (.of k) ⟶ Spec (.of R)) :
    Function.Injective (fun i : Fin 6 => s ≫ (sixMarkedSections R i).val) := by
  exact SixMarkedSectionsDistinctPublicProof20261017.MazurTransfer.Order13SixMarkedSectionsDistinct.six_sections_field_precomposition_injective R h2 k s
#print axioms solution
