-- Prove2me | solution 1 for GlobalTheory.LiePull.lieMult_pull
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:28:19.634808+00:00
-- url     : https://prove2.me/submissions/e8eee153-74cc-4ce3-b32c-f089bebcd0fc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsPushEquiv
import Theorems.Thm_GlobalTheory_LiePull_exists_pushEquiv
import Theorems.Thm_GlobalTheory_LiePull_basis_transport

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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.LiePull
namespace GlobalTheory.LiePull
theorem _root_.solution : ∀ (O : Type) [CommRing O] (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (a : OAct O G) (a' : OAct O G'), IsGrpPullback G' G f φ → (∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act c).left) → ∀ (k : Type) [Field k] (x : Sp k ⟶ S') (τ : O →+* k) (n : ℕ), LieMult a' x τ n ↔ LieMult a (x ≫ f) τ n := by
  intro O _ S S' G G' _ _ f φ a a' h hact k _ x τ n
  obtain ⟨e, he⟩ := exists_pushEquiv h (epsPt x) (spMap (algebraMap k (DualNumber k)) ≫ x ≫ f)
    (Category.assoc _ _ _).symm
  obtain ⟨e₀, he₀⟩ := exists_pushEquiv h (Over.mk x) (x ≫ f) rfl
  have one : (1 : Over.mk (x ≫ f) ⟶ G).left = (1 : Over.mk x ⟶ G').left ≫ φ := by
    rw [← he₀, map_one]
  have sc : ∀ c : k, spMap (epsScale c) ≫ spMap (algebraMap k (DualNumber k)) =
      spMap (algebraMap k (DualNumber k)) := fun c => by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScale, TrivSqZeroExt.algebraMap_eq_inl]
  have fs : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (algebraMap k (DualNumber k)) = 𝟙 _ := by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
    ext a
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hR : ∀ (c : k) (u v : epsPt x ⟶ G'), u.left = spMap (epsScale c) ≫ v.left ↔
      (e u).left = spMap (epsScale c) ≫ (e v).left := fun c u v => by
    rw [he, he]
    refine ⟨fun E => by rw [E]; exact Category.assoc _ _ _, fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w u).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    refine (congrArg (spMap (epsScale c) ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) (sc c))
  have hP : ∀ v : epsPt x ⟶ G', IsLieEigen a' x τ v ↔ IsLieEigen a (x ≫ f) τ (e v) := fun v => by
    refine and_congr ?_ (forall_congr' fun c => ?_)
    · rw [one, he]
      refine ⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm,
        fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩
      refine ((Category.assoc _ _ _).trans ?_).trans (Over.w (1 : Over.mk x ⟶ G')).symm
      refine (congrArg (spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ ·) (Over.w v)).trans ?_
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) fs).trans (Category.id_comp _))
    · have E : e (v ≫ a'.act c) = e v ≫ a.act c := Over.OverMorphism.ext (by
        rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, hact, Category.assoc])
      rw [hR, E]
  constructor
  · exact basis_transport e (R := fun c u v => u.left = spMap (epsScale c) ≫ v.left)
      (R' := fun c u v => u.left = spMap (epsScale c) ≫ v.left) hP hR n
  · exact basis_transport e.symm (R := fun c u v => u.left = spMap (epsScale c) ≫ v.left)
      (R' := fun c u v => u.left = spMap (epsScale c) ≫ v.left)
      (fun v => by rw [hP, e.apply_symm_apply])
      (fun c u v => by rw [hR, e.apply_symm_apply, e.apply_symm_apply]) n
end GlobalTheory.LiePull
