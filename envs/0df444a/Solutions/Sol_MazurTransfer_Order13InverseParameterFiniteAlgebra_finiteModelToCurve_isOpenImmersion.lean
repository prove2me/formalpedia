-- Prove2me | solution 1 for MazurTransfer.Order13InverseParameterFiniteAlgebra.finiteModelToCurve_isOpenImmersion
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T06:29:52.181576+00:00
-- url     : https://prove2.me/submissions/edd9fd09-7e0f-4f93-9b32-45e9a601189d

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
/- Design boundary: the original global inverse finite model comparison is an open immersion into the actual curve.
Named downstream consumer: its actual affine-open isomorphism and inverse FiniteMapData chart. The original private chart-overlap proof is explicitly retained. -/
import Mathlib
import Definitions.Def_MazurTransfer_Order13InverseChartOpen
import Definitions.Def_MazurTransfer_Order13InverseFiniteModelToCurve
import Definitions.Def_MazurTransfer_Order13InverseReciprocalOverlapRange
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry MazurTransfer MazurTorsion
open MazurTorsion.XOneThirteenAffineCurve MazurTorsion.XOneThirteenProjectiveCurve
namespace InverseFiniteModelOpenImmersionOverlapProof20261017
variable (K : Type u) [CommRing K]
private theorem ordinary_ne_reciprocal :
    (XOneThirteenProjectiveCurve.Chart.ordinary :
      XOneThirteenProjectiveCurve.Chart.{u}) ≠
      XOneThirteenProjectiveCurve.Chart.reciprocal := by
  intro h
  cases h

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

theorem reciprocalChartMap_preimage_ordinary_range :
    reciprocalChartMap K ⁻¹' Set.range (ordinaryChartMap K) =
      (PrimeSpectrum.basicOpen (zCoordinate K) : Set (PrimeSpectrum (ReciprocalRing K))) := by
  exact congrArg (fun U : (reciprocalScheme K).Opens => (U : Set (reciprocalScheme K)))
    (reciprocalChartMap_preimage_ordinaryChartMap_opensRange_eq_basicOpen K)
end InverseFiniteModelOpenImmersionOverlapProof20261017
namespace MazurTransfer.Order13InverseParameterFiniteAlgebra
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
theorem reciprocal_finite_mem_ordinary_range_iff (h104 : IsUnit (104 : R))
    (b : PrimeSpectrum (Order13InverseParameterPositiveReciprocalPatch.PatchRing R)) :
    reciprocalToFiniteAffineScheme R h104 b ∈ Set.range (ordinaryParameterToFiniteAffineScheme R) ↔
      Order13InverseParameterPositiveReciprocalPatch.z R ∉ b.asIdeal := by
  rw [ordinaryParameterToFiniteAffineScheme_range]
  change b ∈ (reciprocalToFiniteAffineScheme R h104) ⁻¹ᵁ (PrimeSpectrum.basicOpen (sElement R)) ↔ _
  rw [reciprocalToFiniteAffineScheme_parameter_preimage]
  rfl

omit [IsDomain R] [IsNoetherianRing R] in
theorem reciprocal_curve_mem_original_ordinary_range_iff
    (b : PrimeSpectrum (Order13InverseParameterPositiveReciprocalPatch.PatchRing R)) :
    positiveReciprocalCurveMap R b ∈ Set.range (ordinaryChartMap R) ↔
      Order13InverseParameterPositiveReciprocalPatch.z R ∉ b.asIdeal := by
  have he := Set.ext_iff.mp
    (InverseFiniteModelOpenImmersionOverlapProof20261017.reciprocalChartMap_preimage_ordinary_range R)
      (Spec.map (CommRingCat.ofHom (algebraMap (ReciprocalRing R)
        (Order13InverseParameterPositiveReciprocalPatch.PatchRing R))) b)
  exact he

theorem ordinary_reciprocal_points_identified (h104 : IsUnit (104 : R))
    (a : Spec (.of (MazurTransfer.Order13SingleSectionFiniteAlgebra.ordinaryParameterLocalization R)))
    (b : PrimeSpectrum (Order13InverseParameterPositiveReciprocalPatch.PatchRing R))
    (hab : ordinaryParameterCurveMap R a = positiveReciprocalCurveMap R b) :
    ordinaryParameterToFiniteAffineScheme R a = reciprocalToFiniteAffineScheme R h104 b := by
  have hb : positiveReciprocalCurveMap R b ∈ Set.range (ordinaryChartMap R) := ⟨Spec.map (CommRingCat.ofHom (algebraMap (CoordinateRing R) (MazurTransfer.Order13SingleSectionFiniteAlgebra.ordinaryParameterLocalization R))) a, hab⟩
  have hf : reciprocalToFiniteAffineScheme R h104 b ∈ Set.range (ordinaryParameterToFiniteAffineScheme R) :=
    (reciprocal_finite_mem_ordinary_range_iff R h104 b).mpr
      ((reciprocal_curve_mem_original_ordinary_range_iff R b).mp hb)
  obtain ⟨a',ha'⟩ := hf
  have hv : ordinaryParameterCurveMap R a' = positiveReciprocalCurveMap R b := by
    have hh := congrArg (finiteModelToCurve R h104) ha'
    change (ordinaryParameterToFiniteAffineScheme R ≫ finiteModelToCurve R h104) a' =
      (reciprocalToFiniteAffineScheme R h104 ≫ finiteModelToCurve R h104) b at hh
    rwa [ordinaryParameterToFiniteAffineScheme_finiteModelToCurve,
      reciprocalToFiniteAffineScheme_finiteModelToCurve] at hh
  have haa' : a = a' := (ordinaryParameterCurveMap R).isOpenEmbedding.injective (hab.trans hv.symm)
  rwa [haa']

theorem finiteModelToCurve_injective (h104 : IsUnit (104 : R)) :
    Function.Injective (finiteModelToCurve R h104) := by
  intro p q hpq
  have hp : p ∈ Set.range (ordinaryParameterToFiniteAffineScheme R) ∪
      Set.range (reciprocalToFiniteAffineScheme R h104) := by
    rw [finiteScheme_two_chart_range_cover];trivial
  have hq : q ∈ Set.range (ordinaryParameterToFiniteAffineScheme R) ∪
      Set.range (reciprocalToFiniteAffineScheme R h104) := by
    rw [finiteScheme_two_chart_range_cover];trivial
  rcases hp with ⟨a,rfl⟩ | ⟨b,rfl⟩ <;> rcases hq with ⟨a',rfl⟩ | ⟨b',rfl⟩
  · simp only [← Scheme.Hom.comp_apply,ordinaryParameterToFiniteAffineScheme_finiteModelToCurve] at hpq
    exact congrArg (ordinaryParameterToFiniteAffineScheme R) ((ordinaryParameterCurveMap R).isOpenEmbedding.injective hpq)
  · simp only [← Scheme.Hom.comp_apply,ordinaryParameterToFiniteAffineScheme_finiteModelToCurve,
      reciprocalToFiniteAffineScheme_finiteModelToCurve] at hpq
    exact ordinary_reciprocal_points_identified R h104 a b' hpq
  · simp only [← Scheme.Hom.comp_apply,ordinaryParameterToFiniteAffineScheme_finiteModelToCurve,
      reciprocalToFiniteAffineScheme_finiteModelToCurve] at hpq
    exact (ordinary_reciprocal_points_identified R h104 a' b hpq.symm).symm
  · simp only [← Scheme.Hom.comp_apply,reciprocalToFiniteAffineScheme_finiteModelToCurve] at hpq
    exact congrArg (reciprocalToFiniteAffineScheme R h104)
      ((positiveReciprocalCurveMap R).isOpenEmbedding.injective hpq)

end MazurTransfer.Order13InverseParameterFiniteAlgebra
open MazurTransfer.Order13InverseParameterFiniteAlgebra
theorem solution (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] (h104 : IsUnit (104 : R)) :
    IsOpenImmersion (finiteModelToCurve R h104) := by
  apply IsOpenImmersion.of_openCover_source _ (finiteSchemeOpenCover R h104)
    (finiteModelToCurve_injective R h104)
  intro b
  cases b with
  | true =>
    change IsOpenImmersion (ordinaryParameterToFiniteAffineScheme R ≫ finiteModelToCurve R h104)
    rw [ordinaryParameterToFiniteAffineScheme_finiteModelToCurve]
    infer_instance
  | false =>
    change IsOpenImmersion (reciprocalToFiniteAffineScheme R h104 ≫ finiteModelToCurve R h104)
    rw [reciprocalToFiniteAffineScheme_finiteModelToCurve]
    infer_instance
#print axioms solution
