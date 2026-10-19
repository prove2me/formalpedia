-- Prove2me | solution 1 for MazurTransfer.Order13InverseParameterFiniteAlgebra.actual_chart_intersection_opensRange
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T06:47:25.140572+00:00
-- url     : https://prove2.me/submissions/bfc06e8f-fb24-48c0-ad7c-b06e11d90b9f

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original first section complement and inverse finite-chart open meet exactly in the ordinary parameter localization.
Named downstream consumers: actual parameter basic opens and reciprocity, and unchanged integral FiniteMapData. Uses the Proved public first-chart complement identity and literal positive-infinity image. -/
import Mathlib
import Definitions.Def_MazurTransfer_Order13FirstFiniteChartCanonicalOpen
import Definitions.Def_MazurTransfer_Order13PositiveInfinityReciprocalImage
import Definitions.Def_MazurTransfer_Order13InverseFiniteAffineOpenPresentation
import Definitions.Def_MazurTransfer_Order13InverseReciprocalOverlapRange
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Polynomial
open MazurTorsion.XOneThirteenAffineCurve MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer MazurTransfer.Order13InverseParameterFiniteAlgebra
open MazurTransfer.Order13ActualPositiveInfinityComplement (sectionComplementOpen)
namespace ActualChartIntersectionPublicProof20261017
variable (R : Type u) [CommRing R]
open Order13InverseParameterPositiveReciprocalPatch in
theorem positive_patch_z_mem_forces_w_one (p : PrimeSpectrum (PatchRing R))
    (hz : z R ∈ p.asIdeal) : w R - 1 ∈ p.asIdeal := by
  have he : F R * (F R - 2) = z R *
      (2 * (1 + z R ^ 2) * F R + 4 * z R ^ 3 * (1 + z R)) := by
    linear_combination F_equation R
  have hf : F R ∉ p.asIdeal := by
    intro h
    have hu : IsUnit (F R) := isUnit_of_mul_isUnit_left
      (show IsUnit (F R * r R) by rw [F_mul_r]; exact isUnit_one)
    exact p.isPrime.ne_top (p.asIdeal.eq_top_of_isUnit_mem h hu)
  have hprod : F R * (F R - 2) ∈ p.asIdeal := by
    rw [he]
    exact p.asIdeal.mul_mem_right _ hz
  have hw := (p.isPrime.mem_or_mem hprod).resolve_left hf
  have hz3 : z R ^ 3 ∈ p.asIdeal := p.asIdeal.pow_mem_of_mem hz 3 (by decide)
  have h := p.asIdeal.sub_mem (p.asIdeal.sub_mem hw hz) hz3
  have hF : F R = w R + (1 + z R + z R ^ 3) := by
    simp only [F, f, w, z,
      InverseParameterChartComparisonLibrary.MazurTransfer.Order13InverseParameterPositiveReciprocalPatch.F,
      InverseParameterChartComparisonLibrary.MazurTransfer.Order13InverseParameterPositiveReciprocalPatch.f,
      InverseParameterChartComparisonLibrary.MazurTransfer.Order13InverseParameterPositiveReciprocalPatch.w,
      InverseParameterChartComparisonLibrary.MazurTransfer.Order13InverseParameterPositiveReciprocalPatch.z,
      map_add, map_pow, map_one]
  have hval : F R - 2 - z R - z R ^ 3 = w R - 1 := by rw [hF]; ring
  rwa [hval] at h

theorem reciprocal_preimage_section_image : reciprocalChartMap R ⁻¹'
    Set.range (Order13IntegralSections.infinityMorphism R 1 (by simp)) =
      Set.range (Order13PositiveInfinityReciprocalImage.evaluationSchemeMap R) := by
  change reciprocalChartMap R ⁻¹' Set.range (reciprocalChartMap R ∘
    Order13PositiveInfinityReciprocalImage.evaluationSchemeMap R) = _
  rw [Set.range_comp]
  exact Set.preimage_image_eq _ (reciprocalChartMap R).isOpenEmbedding.injective

theorem ordinary_chart_mem_complement_open (a : PrimeSpectrum (CoordinateRing R)) :
    ordinaryChartMap R a ∈ sectionComplementOpen R := by
  change ordinaryChartMap R a ∈ Set.range (ordinaryChartMap R) ∪
    Set.range (Order13ActualPositiveInfinityComplement.reciprocalPatchChartMap R)
  exact Or.inl ⟨a, rfl⟩

variable [IsDomain R] [IsNoetherianRing R]
theorem positiveReciprocalCurveMap_mem_sectionComplement_iff (h104 : IsUnit (104 : R))
    (p : PrimeSpectrum (Order13InverseParameterPositiveReciprocalPatch.PatchRing R)) :
    positiveReciprocalCurveMap R p ∈ sectionComplementOpen R ↔
      Order13InverseParameterPositiveReciprocalPatch.z R ∉ p.asIdeal := by
  have he := Set.ext_iff.mp (reciprocal_preimage_section_image R)
    (Spec.map (CommRingCat.ofHom (algebraMap (ReciprocalRing R)
      (Order13InverseParameterPositiveReciprocalPatch.PatchRing R))) p)
  change positiveReciprocalCurveMap R p ∈
    Set.range (Order13IntegralSections.positiveInfinitySection R).val ↔ _ at he
  have hmem : (Spec.map (CommRingCat.ofHom (algebraMap (ReciprocalRing R)
      (Order13InverseParameterPositiveReciprocalPatch.PatchRing R))) p) ∈
      Set.range (Order13PositiveInfinityReciprocalImage.evaluationSchemeMap R) ↔
    Order13InverseParameterPositiveReciprocalPatch.z R ∈ p.asIdeal ∧
      Order13InverseParameterPositiveReciprocalPatch.w R - 1 ∈ p.asIdeal := by
    have h := Order13PositiveInfinityReciprocalImage.mem_evaluationSchemeMap_range R
      (PrimeSpectrum.comap (algebraMap (ReciprocalRing R)
        (Order13InverseParameterPositiveReciprocalPatch.PatchRing R)) p)
    change (Spec.map (CommRingCat.ofHom (algebraMap (ReciprocalRing R)
        (Order13InverseParameterPositiveReciprocalPatch.PatchRing R))) p) ∈
        Set.range (Order13PositiveInfinityReciprocalImage.evaluationSchemeMap R) ↔
      algebraMap (ReciprocalRing R) (Order13InverseParameterPositiveReciprocalPatch.PatchRing R)
        (zCoordinate R) ∈ p.asIdeal ∧
      algebraMap (ReciprocalRing R) (Order13InverseParameterPositiveReciprocalPatch.PatchRing R)
        (wCoordinate R - 1) ∈ p.asIdeal at h
    simpa only [Order13InverseParameterPositiveReciprocalPatch.z,
      Order13InverseParameterPositiveReciprocalPatch.w,
      InverseParameterChartComparisonLibrary.MazurTransfer.Order13InverseParameterPositiveReciprocalPatch.z,
      InverseParameterChartComparisonLibrary.MazurTransfer.Order13InverseParameterPositiveReciprocalPatch.w,
      map_sub, map_one] using h
  change positiveReciprocalCurveMap R p ∈
    Order13FirstFiniteChartFromPublicTheorem.chartOpen R ↔ _
  rw [Order13FirstFiniteChartFromPublicTheorem.mem_chartOpen_iff R h104, he, hmem]
  constructor
  · intro h hz
    exact h ⟨hz, positive_patch_z_mem_forces_w_one R p hz⟩
  · intro hz h
    exact hz h.1
theorem reciprocal_finite_mem_ordinary_range_iff (h104 : IsUnit (104 : R))
    (b : PrimeSpectrum (Order13InverseParameterPositiveReciprocalPatch.PatchRing R)) :
    reciprocalToFiniteAffineScheme R h104 b ∈ Set.range (ordinaryParameterToFiniteAffineScheme R) ↔
      Order13InverseParameterPositiveReciprocalPatch.z R ∉ b.asIdeal := by
  rw [ordinaryParameterToFiniteAffineScheme_range]
  change b ∈ (reciprocalToFiniteAffineScheme R h104) ⁻¹ᵁ (PrimeSpectrum.basicOpen (sElement R)) ↔ _
  rw [reciprocalToFiniteAffineScheme_parameter_preimage]
  rfl
end ActualChartIntersectionPublicProof20261017
theorem solution (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] (h104 : IsUnit (104 : R)) :
    sectionComplementOpen R ⊓ inverseChartOpen R = (ordinaryParameterCurveMap R).opensRange := by
  apply TopologicalSpace.Opens.ext
  ext p
  constructor
  · rintro ⟨hpU, hpV⟩
    rcases hpV with ⟨a,rfl⟩ | ⟨b,rfl⟩
    · exact ⟨a,rfl⟩
    · have hz := (ActualChartIntersectionPublicProof20261017.positiveReciprocalCurveMap_mem_sectionComplement_iff R h104 b).mp hpU
      have hb := (ActualChartIntersectionPublicProof20261017.reciprocal_finite_mem_ordinary_range_iff R h104 b).mpr hz
      obtain ⟨a,ha⟩ := hb
      refine ⟨a,?_⟩
      have hc := congrArg (finiteModelToCurve R h104) ha
      change (ordinaryParameterToFiniteAffineScheme R ≫ finiteModelToCurve R h104) a =
        (reciprocalToFiniteAffineScheme R h104 ≫ finiteModelToCurve R h104) b at hc
      rwa [ordinaryParameterToFiniteAffineScheme_finiteModelToCurve,
        reciprocalToFiniteAffineScheme_finiteModelToCurve] at hc
  · rintro ⟨a,rfl⟩
    constructor
    · exact ActualChartIntersectionPublicProof20261017.ordinary_chart_mem_complement_open R
        (Spec.map (CommRingCat.ofHom (algebraMap (CoordinateRing R)
          (Order13SingleSectionFiniteAlgebra.ordinaryParameterLocalization R))) a)
    · left
      exact ⟨a,rfl⟩
#print axioms solution
