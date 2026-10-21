-- Prove2me | solution 1 for MazurTransfer.original_picard_comparison_group_compatibility
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T02:17:07.426963+00:00
-- url     : https://prove2.me/submissions/2f741a29-41bc-4c67-8ebe-0532fae96e3a

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the same canonical actual Picard comparisons preserve the original point group laws over the same rational and local generic fibres.
Named downstream consumer: the actual local generic point equivalence and its integral norm-kernel arithmetic comparison.
-/
import Definitions.Def_MazurTransfer_OriginalPicardComparisonGroupProvidersData20261020
import Theorems.Thm_MazurTransfer_internal_monoid_morphism_of_all_points
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison
open MazurTransfer.Order13GoodPrimeLocalGenericPicardComparison
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13PicardComparisonPublicGroupCompatibility.instGrpObjOverSchemeSpecOfRatMkToBaseLocalGenericPicard_order13PicardComparisonPublicGroupCompatibility
attribute [local instance] MazurTransfer.Order13PicardComparisonPublicGroupCompatibility.instGrpObjOverSchemeSpecOfRatMkToBaseRationalFibre_order13PicardComparisonPublicGroupCompatibility
attribute [local instance] MazurTransfer.Order13PicardComparisonPublicGroupCompatibility.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13PicardComparisonPublicGroupCompatibility
namespace MazurTransfer.OriginalPicardComparisonGroupCompatibilityBoundary20261020
end MazurTransfer.OriginalPicardComparisonGroupCompatibilityBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: apply the accepted public pointwise group-morphism
contract to canonical comparisons for the SAME actual rational Picard,
the selected integral family's rational fibre, and every good-prime local
generic fibre. Named downstream consumer: actual local norm extensions.
-/

noncomputable section
namespace MazurTransfer.OriginalPicardComparisonGroupCompatibilityProof20261020
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13SameIntegralPicardRationalSchemeComparison
open Order13GoodPrimeLocalGenericPicardComparison
open PicardCanonicalRepresentationGroupIsomorphism
open scoped CategoryTheory.MonObj



theorem actual_rational_fibre_comparison_isMonHom :
    IsMonHom actualPicardRationalFibreOverIso.hom := by
  exact MazurTransfer.internal_monoid_morphism_of_all_points _
    (canonicalOverIso_points_one (P := algEquivZeroGroupCut (curveToBase ℚ) infinitySection)
      actualRepresentation rationalFibreRepresentation)
    (canonicalOverIso_points_mul (P := algEquivZeroGroupCut (curveToBase ℚ) infinitySection)
      actualRepresentation rationalFibreRepresentation)

variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)


theorem actual_local_generic_comparison_isMonHom :
    IsMonHom (actualLocalGenericOverIso q hq).hom := by
  exact MazurTransfer.internal_monoid_morphism_of_all_points _
    (canonicalOverIso_points_one (P := algEquivZeroGroupCut (curveToBase ℚ) infinitySection)
      actualRepresentation (localGenericRepresentation q hq))
    (canonicalOverIso_points_mul (P := algEquivZeroGroupCut (curveToBase ℚ) infinitySection)
      actualRepresentation (localGenericRepresentation q hq))

end MazurTransfer.OriginalPicardComparisonGroupCompatibilityProof20261020

theorem solution : (IsMonHom actualPicardRationalFibreOverIso.hom) ∧ (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104), IsMonHom (actualLocalGenericOverIso q hq).hom) := by
  exact ⟨MazurTransfer.OriginalPicardComparisonGroupCompatibilityProof20261020.actual_rational_fibre_comparison_isMonHom, MazurTransfer.OriginalPicardComparisonGroupCompatibilityProof20261020.actual_local_generic_comparison_isMonHom⟩
#print axioms solution
