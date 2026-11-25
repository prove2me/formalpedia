-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.exists_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:38:58.727652+00:00
-- url     : https://prove2.me/submissions/008d1756-27b1-479e-8a3f-43b7b0825393

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsStandardSmoothOfRelativeDimensionAwayJacobian
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MulLeftCompOfPullbackPointEquivMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IrrelevantLeMapLinearGradedMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_isSumTriple_addXYZ
import Theorems.Thm_GlobalTheory_WeierstrassCurve_isSumTriple_diagXYZ
import Theorems.Thm_GlobalTheory_WeierstrassCurve_exists_law_notMem
import Theorems.Thm_GlobalTheory_WeierstrassCurve_IsSumTriple_equation_of_isReduced
import Theorems.Thm_GlobalTheory_WeierstrassCurve_comp_ptOver_eq_fieldAdd
import Theorems.Thm_GlobalTheory_WeierstrassCurve_exists_nhds_eq_ptOver
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineX
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineY
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affinePointEquiv_apply
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affinePointEquiv_symm_zeroOver
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_some
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_toAffineLift
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_zero
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originW
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originZ
import Theorems.Thm_GlobalTheory_WeierstrassCurve_projectivePointEquiv_apply
import Theorems.Thm_GlobalTheory_WeierstrassCurve_projectivePointEquiv_symm_zeroOver
import Theorems.Thm_GlobalTheory_exists_over_hom_of_locally
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineX
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineY
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.affinePointEquiv_apply
attribute [local simp] GlobalTheory.WeierstrassCurve.affinePointEquiv_symm_zeroOver
attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_some
attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_toAffineLift
attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_zero
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originW
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originZ
attribute [local simp] GlobalTheory.WeierstrassCurve.projectivePointEquiv_apply
attribute [local simp] GlobalTheory.WeierstrassCurve.projectivePointEquiv_symm_zeroOver



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open HomogeneousIdeal
universe u
noncomputable section
open GlobalTheory
open GlobalTheory.WeierstrassCurve
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable [W.IsElliptic]
namespace GlobalTheory.WeierstrassCurve
theorem _root_.solution {T : Over (Spec (.of R))} [IsReduced T.left] (p q : T ⟶ schemeOver W) :
    ∃ s : T ⟶ schemeOver W, ∀ (k : Type u) [Field k] [Algebra R k] (x : specOver R k ⟶ T),
      x ≫ s = fieldAdd W k (x ≫ p) (x ≫ q) := by
  have : IsSeparated (schemeOver W).hom := inferInstanceAs (IsSeparated (toSpec W))
  refine exists_over_hom_of_locally (fun k _ _ x => fieldAdd W k (x ≫ p) (x ≫ q)) fun t => ?_
  obtain ⟨A, _, _, j, P, Q, hP, hQ, hj, ⟨y, rfl⟩, eP, eQ⟩ := exists_nhds_eq_ptOver W p q t
  have : _root_.IsReduced A :=
    (affine_isReduced_iff (.of A)).mp (isReduced_of_isOpenImmersion j.left)
  obtain ⟨S, hS, i, hi⟩ : ∃ S, IsSumTriple (W.baseChange A) P Q S ∧ ∃ i, S i ∉ y.asIdeal := by
    rcases @exists_law_notMem _ _ _ _ _ _ hP hQ y.asIdeal y.isPrime with h | h
    exacts [⟨_, isSumTriple_addXYZ hP.equation hQ.equation, h⟩,
      ⟨_, isSumTriple_diagXYZ hP.equation hQ.equation, h⟩]
  let g : A →ₐ[R] Localization.Away (S i) := IsScalarTower.toAlgHom R A _
  have hS' : IsUnimodularSol (W.baseChange (Localization.Away (S i))) (g ∘ S) :=
    .of_isUnit ((hS.baseChange g).equation_of_isReduced (hP.baseChange g) (hQ.baseChange g)) i
      (IsLocalization.Away.algebraMap_isUnit (S i))
  have hg : IsOpenImmersion (specOverMap g).left := IsOpenImmersion.of_isLocalization (S i)
  refine ⟨_, specOverMap g ≫ j, inferInstanceAs (IsOpenImmersion ((specOverMap g).left ≫ j.left)),
    ptOver W _ hS', ?_, fun k _ _ x => ?_⟩
  · obtain ⟨z, hz⟩ :=
      (PrimeSpectrum.localization_away_comap_range (Localization.Away (S i)) (S i)).ge hi
    exact ⟨z, congrArg j.left hz⟩
  · simp only [Category.assoc, eP, eQ, specOverMap_ptOver]
    exact comp_ptOver_eq_fieldAdd W _ _ _ (hS.baseChange g) k x
end GlobalTheory.WeierstrassCurve
