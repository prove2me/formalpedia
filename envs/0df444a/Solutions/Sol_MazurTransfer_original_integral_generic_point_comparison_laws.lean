-- Prove2me | solution 1 for MazurTransfer.original_integral_generic_point_comparison_laws
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T02:38:42.842355+00:00
-- url     : https://prove2.me/submissions/6a6a1e21-51e8-47f3-856d-c7bef62a6d07

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the same actual rational Picard and selected integral local Picard have their original point equivalence on every rational test scheme, preserving identity, multiplication, precomposition and every original integral norm extension.
Named downstream consumer: the actual arithmetic field-point and norm-kernel Galois comparison.
-/
import Definitions.Def_MazurTransfer_OriginalIntegralGenericPointComparisonData20261020
import Definitions.Def_MazurTransfer_Order13GoodPrimeIntegralNormExtensionsData
import Theorems.Thm_MazurTransfer_original_picard_comparison_group_compatibility
import Theorems.Thm_MazurTransfer_original_generic_local_group_pointwise_unit_and_scalar
import Theorems.Thm_MazurTransfer_Order13GoodPrimeGenericNormGroupLaws_generic_group_law_multiplications_equal
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard GoodReductionJacobian NeronModelInfra
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open MazurTransfer.Order13GoodPrimeLocalPicardModels MazurTransfer.Order13LocalIntegralCoefficientMaps
open MazurTransfer.Order13GoodPrimeLocalGenericPicardComparison MazurTransfer.Order13GoodPrimeIntegralNormExtensions
open MazurTransfer.Order13IntegralGenericPointComparison
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13IntegralGenericPointComparison.instGrpObjOverSchemeSpecOfRatMkToBaseLocalGenericPicard_order13IntegralGenericPointComparison
attribute [local instance] MazurTransfer.Order13IntegralGenericPointComparison.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13IntegralGenericPointComparison
namespace MazurTransfer.OriginalIntegralGenericPointComparisonBoundary20261020
end MazurTransfer.OriginalIntegralGenericPointComparisonBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: compare points of the SAME selected integral Picard
with the fixed actual rational Picard on every rational test scheme,
using its actual generic fibre and the retained canonical over-isomorphism.
Retain multiplication, zero, every test-scheme precomposition and the
SAME selected integral extensions of actual rational endomorphisms.
Named downstream consumer: arithmetic Galois comparison of norm kernels.
-/

noncomputable section
namespace MazurTransfer.OriginalIntegralGenericPointComparisonProof20261020
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open Order13LocalIntegralCoefficientMaps Order13GoodPrimeLocalPicardModels
open Order13GoodPrimeLocalGenericPicardComparison Order13GoodPrimeLocalGenericGroupIdentity
open Order13GoodPrimeIntegralNormExtensions
open Order13GoodPrimeGenericNormGroupLaws Order13PicardComparisonPublicGroupCompatibility
open Order13ActualPicardDiamondSchemeEndomorphism Order13SameIntegralPicardRationalSchemeComparison
open scoped CategoryTheory.MonObj
variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)















theorem actualToLocal_one {T : Scheme} (t : T ⟶ Spec (CommRingCat.of ℚ)) :
    actualToLocal q hq (1 : Over.mk t ⟶ Over.mk actualPicard.toBase) =
      (localLaw q hq).one (t ≫ localGenericInclusion q) := by
  letI := (MazurTransfer.original_picard_comparison_group_compatibility).2 q hq
  have h : overHomToSchemeHomOver
      ((1 : Over.mk t ⟶ Over.mk actualPicard.toBase) ≫ (actualLocalGenericOverIso q hq).hom) =
      (genericLocalLaw q hq).one t := by
    rw [(MazurTransfer.original_generic_local_group_pointwise_unit_and_scalar).1]
    change overHomToSchemeHomOver (_ ≫ _) = overHomToSchemeHomOver 1
    rw [MonObj.one_comp]
  have h' := congrArg (RelativeGroupLaw.baseChangePointToBase
    (f := (localPicard q hq).toBase) (localGenericInclusion q)) h
  exact h'.trans ((localLaw q hq).baseChangePointToBase_one (localGenericInclusion q) t)

theorem actualToLocal_mul {T : Scheme} (t : T ⟶ Spec (CommRingCat.of ℚ))
    (a b : Over.mk t ⟶ Over.mk actualPicard.toBase) :
    actualToLocal q hq (a * b) = (localLaw q hq).mul (t ≫ localGenericInclusion q)
      (actualToLocal q hq a) (actualToLocal q hq b) := by
  letI := (MazurTransfer.original_picard_comparison_group_compatibility).2 q hq
  have h : overHomToSchemeHomOver ((a * b) ≫ (actualLocalGenericOverIso q hq).hom) =
      (genericLocalLaw q hq).mul t
        (overHomToSchemeHomOver (a ≫ (actualLocalGenericOverIso q hq).hom))
        (overHomToSchemeHomOver (b ≫ (actualLocalGenericOverIso q hq).hom)) := by
    erw [generic_group_law_multiplications_equal]
    change overHomToSchemeHomOver (_ ≫ _) = overHomToSchemeHomOver ((_ ≫ _) * (_ ≫ _))
    rw [MonObj.mul_comp]
  have h' := congrArg (RelativeGroupLaw.baseChangePointToBase
    (f := (localPicard q hq).toBase) (localGenericInclusion q)) h
  exact h'.trans ((localLaw q hq).baseChangePointToBase_mul (localGenericInclusion q) t _ _)

theorem actualToLocal_precomp {T T' : Scheme} (t : T ⟶ Spec (CommRingCat.of ℚ))
    (t' : T' ⟶ Spec (CommRingCat.of ℚ)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (a : Over.mk t ⟶ Over.mk actualPicard.toBase) :
    actualToLocal q hq ((Over.homMk ψ hψ : Over.mk t' ⟶ Over.mk t) ≫ a) =
      GoodReductionJacobian.schemeHomOverComp ψ (by rw [← Category.assoc, hψ])
        (actualToLocal q hq a) := by
  apply Subtype.ext
  change ((ψ ≫ a.left) ≫ (actualLocalGenericOverIso q hq).hom.left) ≫
    pullback.fst (localPicard q hq).toBase (localGenericInclusion q) =
    ψ ≫ ((a.left ≫ (actualLocalGenericOverIso q hq).hom.left) ≫
      pullback.fst (localPicard q hq).toBase (localGenericInclusion q))
  exact Category.assoc ψ (a.left ≫ (actualLocalGenericOverIso q hq).hom.left)
    (pullback.fst (localPicard q hq).toBase (localGenericInclusion q))

theorem integralNorm_generic_point_compat {T : Scheme}
    (t : T ⟶ Spec (CommRingCat.of ℚ))
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
    (x : SchemeHomOver t (localGenericPicard q hq).toBase) :
    RelativeGroupLaw.baseChangePointToBase (f := (localPicard q hq).toBase)
      (localGenericInclusion q) (NeronModelInfra.schemeHomOverComp x (localGenericNorm q hq φ)) =
      NeronModelInfra.schemeHomOverComp
        (RelativeGroupLaw.baseChangePointToBase (f := (localPicard q hq).toBase)
          (localGenericInclusion q) x) (integralNorm q hq φ) := by
  have h := RelativeGroupLaw.baseChangePointToBase_comp_genericFibreRestrict ℚ
    (integralNorm q hq φ) x
  have heq := congrArg (fun m : SchemeHomOver (localGenericPicard q hq).toBase
      (localGenericPicard q hq).toBase =>
    RelativeGroupLaw.baseChangePointToBase (f := (localPicard q hq).toBase)
      (localGenericInclusion q) (NeronModelInfra.schemeHomOverComp x m))
      (integralNorm_restrict q hq φ)
  exact heq.symm.trans h

theorem actualToLocal_norm {T : Scheme} (t : T ⟶ Spec (CommRingCat.of ℚ))
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
    (a : Over.mk t ⟶ Over.mk actualPicard.toBase) :
    actualToLocal q hq (a ≫ φ) =
      NeronModelInfra.schemeHomOverComp (actualToLocal q hq a) (integralNorm q hq φ) := by
  have h : overHomToSchemeHomOver ((a ≫ φ) ≫ (actualLocalGenericOverIso q hq).hom) =
      NeronModelInfra.schemeHomOverComp
        (overHomToSchemeHomOver (a ≫ (actualLocalGenericOverIso q hq).hom))
        (localGenericNorm q hq φ) := by
    apply Subtype.ext
    change ((a ≫ φ) ≫ (actualLocalGenericOverIso q hq).hom).left =
      ((a ≫ (actualLocalGenericOverIso q hq).hom) ≫
        ((actualLocalGenericOverIso q hq).inv ≫ φ ≫ (actualLocalGenericOverIso q hq).hom)).left
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have h' := congrArg (RelativeGroupLaw.baseChangePointToBase
    (f := (localPicard q hq).toBase) (localGenericInclusion q)) h
  exact h'.trans (integralNorm_generic_point_compat q hq t φ
    (overHomToSchemeHomOver (a ≫ (actualLocalGenericOverIso q hq).hom)))

end MazurTransfer.OriginalIntegralGenericPointComparisonProof20261020

theorem solution : (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104), ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of ℚ)),
actualToLocal q hq (1 : Over.mk t ⟶ Over.mk actualPicard.toBase) =
      (localLaw q hq).one (t ≫ localGenericInclusion q)) ∧ (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104), ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of ℚ))
    (a b : Over.mk t ⟶ Over.mk actualPicard.toBase),
actualToLocal q hq (a * b) = (localLaw q hq).mul (t ≫ localGenericInclusion q)
      (actualToLocal q hq a) (actualToLocal q hq b)) ∧ (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104), ∀ {T T' : Scheme} (t : T ⟶ Spec (CommRingCat.of ℚ))
    (t' : T' ⟶ Spec (CommRingCat.of ℚ)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (a : Over.mk t ⟶ Over.mk actualPicard.toBase),
actualToLocal q hq ((Over.homMk ψ hψ : Over.mk t' ⟶ Over.mk t) ≫ a) =
      GoodReductionJacobian.schemeHomOverComp ψ (by rw [← Category.assoc, hψ])
        (actualToLocal q hq a)) ∧ (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104), ∀ {T : Scheme}
    (t : T ⟶ Spec (CommRingCat.of ℚ))
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
    (x : SchemeHomOver t (localGenericPicard q hq).toBase),
RelativeGroupLaw.baseChangePointToBase (f := (localPicard q hq).toBase)
      (localGenericInclusion q) (NeronModelInfra.schemeHomOverComp x (localGenericNorm q hq φ)) =
      NeronModelInfra.schemeHomOverComp
        (RelativeGroupLaw.baseChangePointToBase (f := (localPicard q hq).toBase)
          (localGenericInclusion q) x) (integralNorm q hq φ)) ∧ (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104), ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of ℚ))
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
    (a : Over.mk t ⟶ Over.mk actualPicard.toBase),
actualToLocal q hq (a ≫ φ) =
      NeronModelInfra.schemeHomOverComp (actualToLocal q hq a) (integralNorm q hq φ)) := by
  exact ⟨MazurTransfer.OriginalIntegralGenericPointComparisonProof20261020.actualToLocal_one, MazurTransfer.OriginalIntegralGenericPointComparisonProof20261020.actualToLocal_mul, MazurTransfer.OriginalIntegralGenericPointComparisonProof20261020.actualToLocal_precomp, MazurTransfer.OriginalIntegralGenericPointComparisonProof20261020.integralNorm_generic_point_compat, MazurTransfer.OriginalIntegralGenericPointComparisonProof20261020.actualToLocal_norm⟩
#print axioms solution
