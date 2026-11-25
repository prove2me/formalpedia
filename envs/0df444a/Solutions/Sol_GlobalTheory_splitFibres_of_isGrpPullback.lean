-- Prove2me | solution 1 for GlobalTheory.splitFibres_of_isGrpPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:00:53.816354+00:00
-- url     : https://prove2.me/submissions/9bea6906-740a-4f91-9720-fa835ddb269d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFiniteSeparableCompositum
import Theorems.Thm_GlobalTheory_exists_finite_separable_compositum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_grpPullback_iso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGt_of_iso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : Out.GtBaseChangeSt → ∀ (X X' : Scheme.{0}) (f : X' ⟶ X) (G : Over X) [GrpObj G] (G' : Over X') [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → (∀ x : X, ∃ (k : Type) (_ : Field k) (_ : Algebra (X.residueField x) k), FiniteDimensional (X.residueField x) k ∧ Algebra.IsSeparable (X.residueField x) k ∧ ∃ S : SplitExt (Sp k), S.IsGt ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) k)) ≫ X.fromSpecResidueField x)).obj G)) → (∀ x : X', ∃ (k : Type) (_ : Field k) (_ : Algebra (X'.residueField x) k), FiniteDimensional (X'.residueField x) k ∧ Algebra.IsSeparable (X'.residueField x) k ∧ ∃ S : SplitExt (Sp k), S.IsGt ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (X'.residueField x) k)) ≫ X'.fromSpecResidueField x)).obj G')) := by
  intro hB X X' f G _ G' _ φ hφ hS x'
  obtain ⟨k, _, _, hfin, hsep, S, hGt⟩ := hS (f x')
  obtain ⟨k', _, _, g, h₁, h₂, hg⟩ :=
    exists_finite_separable_compositum (X.residueField (f x')) (X'.residueField x') k (f.residueFieldMap x').hom
  refine ⟨k', inferInstance, inferInstance, h₁, h₂, ?_⟩
  have key : spMap g ≫ Spec.map (CommRingCat.ofHom (algebraMap (X.residueField (f x')) k)) ≫
      X.fromSpecResidueField (f x') =
      (Spec.map (CommRingCat.ofHom (algebraMap (X'.residueField x') k')) ≫ X'.fromSpecResidueField x') ≫ f := by
    have a₁ : spMap g ≫ Spec.map (CommRingCat.ofHom (algebraMap (X.residueField (f x')) k)) =
        spMap (algebraMap (X'.residueField x') k') ≫ Spec.map (f.residueFieldMap x') :=
      (spMap_comp _ _).symm.trans ((congrArg spMap hg).trans (spMap_comp _ _))
    rw [← Category.assoc, a₁, Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      Category.assoc]
  obtain ⟨S', -, -, -, -, hGt'⟩ := hB _ _ (spMap g) S _ hGt
  refine ⟨S', ?_⟩
  have : IsMonHom (pullCompIso (spMap g) (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField (f x')) k)) ≫
      X.fromSpecResidueField (f x')) G).symm.hom := by
    show IsMonHom (pullCompIso _ _ _).inv
    infer_instance
  have h₀ := isGt_of_iso (pullCompIso (spMap g) _ G).symm hGt'
  rw [key] at h₀
  have h₃ := isGt_of_iso (pullCompIso _ f G) h₀
  obtain ⟨e, he, -⟩ := grpPullback_iso (isGrpPullback_pullback G f) hφ
  have : IsMonHom ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (X'.residueField x') k')) ≫
      X'.fromSpecResidueField x')).mapIso e).hom := by
    rw [Functor.mapIso_hom]
    infer_instance
  exact isGt_of_iso ((Over.pullback _).mapIso e) h₃
end GlobalTheory
