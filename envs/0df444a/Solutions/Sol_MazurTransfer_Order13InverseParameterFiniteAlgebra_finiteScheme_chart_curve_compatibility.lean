-- Prove2me | solution 1 for MazurTransfer.Order13InverseParameterFiniteAlgebra.finiteScheme_chart_curve_compatibility
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T06:22:38.241859+00:00
-- url     : https://prove2.me/submissions/a9cb2fab-e2e1-4344-87ca-34fc72209c01

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: all pullback overlaps of the actual inverse finite atlas map compatibly into the actual curve.
Named downstream consumer: the original finiteModelToCurve gluing constructor. Original proof bodies and literal maps are retained. -/
import Mathlib
import Definitions.Def_MazurTransfer_Order13InverseOverlapSchemeMaps
import Definitions.Def_MazurTransfer_Order13InverseFiniteAtlasTargetMaps
import Theorems.Thm_MazurTransfer_Order13SingleSectionFiniteAlgebra_ordinary_reciprocal_glue_base
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MazurTorsion.XOneThirteenAffineCurve MazurTorsion.XOneThirteenProjectiveCurve
namespace MazurTransfer.Order13InverseParameterFiniteAlgebra
open Order13SingleSectionFiniteAlgebra (ordinaryParameterLocalization)
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
omit [IsDomain R] [IsNoetherianRing R] in
theorem ordinaryParameterToFiniteAffineScheme_eq_Spec :
    ordinaryParameterToFiniteAffineScheme R = Spec.map (CommRingCat.ofHom (inclusion R).toRingHom) := by
  change Spec.map (CommRingCat.ofHom (parameterLocalizationEquiv R).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (candidateAlgebra R) (parameterLocalization R))) = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact localizedInclusion_algebraMap R

theorem ordinaryInfinityChartMap_comparison (h104 : IsUnit (104 : R)) :
    ordinaryInfinityChartMap R ≫ ordinaryParameterToFiniteAffineScheme R =
      ordinaryInfinityToReciprocalPatch R h104 ≫ reciprocalToFiniteAffineScheme R h104 := by
  rw [ordinaryParameterToFiniteAffineScheme_eq_Spec, ← reciprocalFiniteChartRingHom_Spec]
  change Spec.map (CommRingCat.ofHom (algebraMap (ordinaryParameterLocalization R) (ordinaryInfinityLocalization R))) ≫
    Spec.map (CommRingCat.ofHom (inclusion R).toRingHom) =
    Spec.map (CommRingCat.ofHom
      ((infinityLocalizedInclusion R).comp (recoveredReciprocalPatchEquiv R h104).toAlgHom).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (reciprocalFiniteChartRingHom R h104))
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  change ordinaryInfinityMap R (inclusion R c) =
    infinityLocalizedInclusion R ((recoveredReciprocalPatchEquiv R h104)
      ((recoveredReciprocalPatchEquiv R h104).symm
        (algebraMap (candidateAlgebra R) (infinityLocalization R) c)))
  rw [AlgEquiv.apply_symm_apply,infinityLocalizedInclusion_algebraMap]

theorem ordinaryInfinityChartMap_preimage (h104 : IsUnit (104 : R)) :
    letI := reciprocalToFiniteAffineScheme_isOpenImmersion R h104
    letI : IsOpenImmersion (ordinaryInfinityChartMap R) :=
      IsOpenImmersion.of_isLocalization (inclusion R (infinityPatchElement R))
    (ordinaryParameterToFiniteAffineScheme R) ⁻¹ᵁ
      (reciprocalToFiniteAffineScheme R h104).opensRange = (ordinaryInfinityChartMap R).opensRange := by
  let := reciprocalToFiniteAffineScheme_isOpenImmersion R h104
  let : IsOpenImmersion (ordinaryInfinityChartMap R) :=
    IsOpenImmersion.of_isLocalization (inclusion R (infinityPatchElement R))
  rw [ordinaryParameterToFiniteAffineScheme_eq_Spec]
  apply TopologicalSpace.Opens.ext
  ext a
  change Spec.map (CommRingCat.ofHom (inclusion R).toRingHom) a ∈ Set.range (reciprocalToFiniteAffineScheme R h104) ↔
    a ∈ Set.range (PrimeSpectrum.comap (algebraMap (ordinaryParameterLocalization R) (ordinaryInfinityLocalization R)))
  rw [reciprocalToFiniteAffineScheme_range,
    PrimeSpectrum.localization_away_comap_range (ordinaryInfinityLocalization R) (inclusion R (infinityPatchElement R))]
  change inclusion R (infinityPatchElement R) ∉ a.asIdeal ↔
    inclusion R (infinityPatchElement R) ∉ a.asIdeal
  rfl

theorem ordinaryInfinityOverlap_isPullback (h104 : IsUnit (104 : R)) :
    IsPullback (ordinaryInfinityToReciprocalPatch R h104) (ordinaryInfinityChartMap R)
      (reciprocalToFiniteAffineScheme R h104) (ordinaryParameterToFiniteAffineScheme R) := by
  let := reciprocalToFiniteAffineScheme_isOpenImmersion R h104
  let : IsOpenImmersion (ordinaryInfinityChartMap R) :=
    IsOpenImmersion.of_isLocalization (inclusion R (infinityPatchElement R))
  exact IsOpenImmersion.isPullback _ _ _ _
    (ordinaryInfinityChartMap_comparison R h104) (ordinaryInfinityChartMap_preimage R h104)

theorem ordinaryInfinityChartMap_overlap_factorization :
    ordinaryInfinityChartMap R ≫ Spec.map (CommRingCat.ofHom
      (algebraMap (CoordinateRing R) (ordinaryParameterLocalization R))) =
    Spec.map (CommRingCat.ofHom (ordinaryOverlapToInfinity R).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (CoordinateRing R) (OrdinaryOverlapRing R))) := by
  change Spec.map (CommRingCat.ofHom (algebraMap (ordinaryParameterLocalization R)
      (ordinaryInfinityLocalization R))) ≫ _ = _
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact (ordinaryOverlapToInfinity_algebraMap R c).symm

theorem ordinaryInfinityToReciprocalPatch_overlap_factorization (h104 : IsUnit (104 : R)) :
    ordinaryInfinityToReciprocalPatch R h104 ≫ Spec.map (CommRingCat.ofHom
      (algebraMap (ReciprocalRing R) (Order13InverseParameterPositiveReciprocalPatch.PatchRing R))) =
      Spec.map (CommRingCat.ofHom (ordinaryOverlapToInfinity R).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (reciprocalToOrdinaryBase R).toRingHom) := by
  change Spec.map (CommRingCat.ofHom
      ((infinityLocalizedInclusion R).comp (recoveredReciprocalPatchEquiv R h104).toAlgHom).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (ReciprocalRing R) (Order13InverseParameterPositiveReciprocalPatch.PatchRing R))) =
      Spec.map (CommRingCat.ofHom (ordinaryOverlapToInfinity R).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (reciprocalToOrdinaryBase R).toRingHom)
  rw [← Spec.map_comp,← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change infinityLocalizedInclusion R
    (recoveredReciprocalPatch R (two_isUnit_of_104 R h104)
      (algebraMap (ReciprocalRing R) (Order13InverseParameterPositiveReciprocalPatch.PatchRing R) a)) =
    ordinaryOverlapToInfinity R (reciprocalToOrdinaryBase R a)
  rw [recoveredReciprocalPatch_algebraMap]
  exact DFunLike.congr_fun (recovered_reciprocal_ordinary_comparison_square R) a

theorem finiteScheme_concrete_overlap_curve_compatibility (h104 : IsUnit (104 : R)) :
    ordinaryInfinityChartMap R ≫ ordinaryParameterCurveMap R =
      ordinaryInfinityToReciprocalPatch R h104 ≫ positiveReciprocalCurveMap R := by
  rw [ordinaryParameterCurveMap, ← Category.assoc, ordinaryInfinityChartMap_overlap_factorization,
    Category.assoc, Order13SingleSectionFiniteAlgebra.ordinary_reciprocal_glue_base]
  rw [positiveReciprocalCurveMap]
  simpa only [Category.assoc] using congrArg (fun f => f ≫ reciprocalChartMap R)
    (ordinaryInfinityToReciprocalPatch_overlap_factorization R h104).symm

theorem finiteScheme_mixed_chart_curve_compatibility (h104 : IsUnit (104 : R)) :
    pullback.fst (ordinaryParameterToFiniteAffineScheme R) (reciprocalToFiniteAffineScheme R h104) ≫
      ordinaryParameterCurveMap R =
    pullback.snd (ordinaryParameterToFiniteAffineScheme R) (reciprocalToFiniteAffineScheme R h104) ≫
      positiveReciprocalCurveMap R := by
  have h := (ordinaryInfinityOverlap_isPullback R h104).flip
  apply (cancel_epi h.isoPullback.hom).mp
  simpa only [← Category.assoc,IsPullback.isoPullback_hom_fst,IsPullback.isoPullback_hom_snd]
    using finiteScheme_concrete_overlap_curve_compatibility R h104

end MazurTransfer.Order13InverseParameterFiniteAlgebra
open MazurTransfer.Order13InverseParameterFiniteAlgebra
theorem solution (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] (h104 : IsUnit (104 : R)) (i j : Bool) :
    pullback.fst (finiteSchemeChartMap R h104 i) (finiteSchemeChartMap R h104 j) ≫
      finiteSchemeChartToCurve R i =
    pullback.snd (finiteSchemeChartMap R h104 i) (finiteSchemeChartMap R h104 j) ≫
      finiteSchemeChartToCurve R j := by
  cases i with
  | false =>
    cases j with
    | false =>
      let := reciprocalToFiniteAffineScheme_isOpenImmersion R h104
      have he : pullback.fst (reciprocalToFiniteAffineScheme R h104)
          (reciprocalToFiniteAffineScheme R h104) = pullback.snd _ _ :=
        (cancel_mono (reciprocalToFiniteAffineScheme R h104)).mp pullback.condition
      change pullback.fst (reciprocalToFiniteAffineScheme R h104) (reciprocalToFiniteAffineScheme R h104) ≫ positiveReciprocalCurveMap R = pullback.snd (reciprocalToFiniteAffineScheme R h104) (reciprocalToFiniteAffineScheme R h104) ≫ positiveReciprocalCurveMap R
      rw [he]
    | true =>
      change pullback.fst (reciprocalToFiniteAffineScheme R h104) (ordinaryParameterToFiniteAffineScheme R) ≫
        positiveReciprocalCurveMap R = pullback.snd (reciprocalToFiniteAffineScheme R h104)
          (ordinaryParameterToFiniteAffineScheme R) ≫ ordinaryParameterCurveMap R
      apply (cancel_epi (pullbackSymmetry (ordinaryParameterToFiniteAffineScheme R)
        (reciprocalToFiniteAffineScheme R h104)).hom).mp
      rw [← Category.assoc,← Category.assoc,
        pullbackSymmetry_hom_comp_fst,pullbackSymmetry_hom_comp_snd]
      exact (finiteScheme_mixed_chart_curve_compatibility R h104).symm
  | true =>
    cases j with
    | false => exact finiteScheme_mixed_chart_curve_compatibility R h104
    | true =>
      let := ordinaryParameterToFiniteAffineScheme_isOpenImmersion R
      have he : pullback.fst (ordinaryParameterToFiniteAffineScheme R)
          (ordinaryParameterToFiniteAffineScheme R) = pullback.snd _ _ :=
        (cancel_mono (ordinaryParameterToFiniteAffineScheme R)).mp pullback.condition
      change pullback.fst (ordinaryParameterToFiniteAffineScheme R) (ordinaryParameterToFiniteAffineScheme R) ≫ ordinaryParameterCurveMap R = pullback.snd (ordinaryParameterToFiniteAffineScheme R) (ordinaryParameterToFiniteAffineScheme R) ≫ ordinaryParameterCurveMap R
      rw [he]
#print axioms solution
