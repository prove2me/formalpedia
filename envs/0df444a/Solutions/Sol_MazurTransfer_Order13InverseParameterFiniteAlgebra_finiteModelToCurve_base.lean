-- Prove2me | solution 1 for MazurTransfer.Order13InverseParameterFiniteAlgebra.finiteModelToCurve_base
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T06:31:02.730865+00:00
-- url     : https://prove2.me/submissions/9a892a47-093f-46aa-8e77-96f456564278

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original glued inverse finite-model comparison preserves its actual structural base morphism.
Named downstream consumer: the inverse affine-open structural R-algebra section comparison and actual integral FiniteMapData. -/
import Mathlib
import Definitions.Def_MazurTransfer_Order13InverseFiniteModelBaseMaps
import Definitions.Def_MazurTransfer_Order13InverseFiniteModelToCurve
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Polynomial
open MazurTorsion.XOneThirteenAffineCurve MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer MazurTransfer.Order13InverseParameterFiniteAlgebra
namespace InverseFiniteModelBasePublicProof20261017
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

theorem ordinaryParameterToFiniteAffineScheme_base :
    ordinaryParameterToFiniteAffineScheme R ≫ inverseFiniteAffineSchemeToBase R =
      ordinaryParameterCurveMap R ≫ curveToBase R := by
  rw [ordinaryParameterCurveMap_base, ordinaryParameterToFiniteAffineScheme_eq_Spec]
  unfold inverseFiniteAffineSchemeToBase inverseFiniteAffineMap
    InverseParameterChartComparisonLibrary.MazurTransfer.Order13InverseParameterFiniteAlgebra.inverseFiniteAffineMap
  dsimp only [inverseFiniteAffineScheme,
    InverseParameterChartComparisonLibrary.MazurTransfer.Order13InverseParameterFiniteAlgebra.inverseFiniteAffineScheme]
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact (inclusion R).commutes c

theorem reciprocalToFiniteAffineScheme_base (h104 : IsUnit (104 : R)) :
    reciprocalToFiniteAffineScheme R h104 ≫ inverseFiniteAffineSchemeToBase R =
      positiveReciprocalCurveMap R ≫ curveToBase R := by
  rw [positiveReciprocalCurveMap_base, ← reciprocalFiniteChartRingHom_Spec]
  unfold inverseFiniteAffineSchemeToBase inverseFiniteAffineMap
    InverseParameterChartComparisonLibrary.MazurTransfer.Order13InverseParameterFiniteAlgebra.inverseFiniteAffineMap
  dsimp only [inverseFiniteAffineScheme,
    InverseParameterChartComparisonLibrary.MazurTransfer.Order13InverseParameterFiniteAlgebra.inverseFiniteAffineScheme]
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact (candidateToReciprocalPatch R h104).commutes c

end InverseFiniteModelBasePublicProof20261017
open InverseFiniteModelBasePublicProof20261017
theorem solution (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] (h104 : IsUnit (104 : R)) :
    finiteModelToCurve R h104 ≫ curveToBase R = inverseFiniteAffineSchemeToBase R := by
  apply (finiteSchemeOpenCover R h104).hom_ext
  intro b
  cases b with
  | true =>
    change ordinaryParameterToFiniteAffineScheme R ≫ finiteModelToCurve R h104 ≫ curveToBase R =
      ordinaryParameterToFiniteAffineScheme R ≫ inverseFiniteAffineSchemeToBase R
    rw [← Category.assoc, ordinaryParameterToFiniteAffineScheme_finiteModelToCurve,
      ordinaryParameterToFiniteAffineScheme_base]
  | false =>
    change reciprocalToFiniteAffineScheme R h104 ≫ finiteModelToCurve R h104 ≫ curveToBase R =
      reciprocalToFiniteAffineScheme R h104 ≫ inverseFiniteAffineSchemeToBase R
    rw [← Category.assoc, reciprocalToFiniteAffineScheme_finiteModelToCurve,
      reciprocalToFiniteAffineScheme_base]
#print axioms solution
