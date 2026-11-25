-- Prove2me | solution 1 for GlobalTheory.lieMult_iff_of_isGrpPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:11:42.12534+00:00
-- url     : https://prove2.me/submissions/cf68809b-fe0d-4206-8433-282717a16f6a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsMulEquivOfIsGrpPullback
import Theorems.Thm_GlobalTheory_exists_mulEquiv_of_isGrpPullback
import Theorems.Thm_GlobalTheory_spMap_epsScale_comp_algebraMap
import Theorems.Thm_GlobalTheory_spMap_fstHom_comp_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
variable {k : Type} [Field k]
namespace GlobalTheory
theorem _root_.solution (h : IsGrpPullback G' G f φ) {O : Type} [CommRing O] (act' : OAct O G')
    (act : OAct O G) (hact : ∀ a, (act'.act a).left ≫ φ = φ ≫ (act.act a).left) (x : Sp k ⟶ S') (τ : O →+* k)
    (n : ℕ) : LieMult act' x τ n ↔ LieMult act (x ≫ f) τ n := by
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback h (spMap (algebraMap k (DualNumber k)) ≫ x)
    (spMap (algebraMap k (DualNumber k)) ≫ x ≫ f) (Category.assoc _ _ _).symm
  obtain ⟨e₀, he₀⟩ := exists_mulEquiv_of_isGrpPullback h x (x ≫ f) rfl
  have one : (1 : Over.mk (x ≫ f) ⟶ G).left = (1 : Over.mk x ⟶ G').left ≫ φ := by
    rw [← he₀, map_one]
  have scale : ∀ (c : k) (u v : epsPt x ⟶ G'),
      u.left = spMap (epsScale c) ≫ v.left ↔ (e u).left = spMap (epsScale c) ≫ (e v).left := by
    intro c u v
    rw [he, he, ← Category.assoc]
    refine ⟨fun huv => congrArg (· ≫ φ) huv, fun huv => h.1.hom_ext huv ?_⟩
    refine (Over.w u).trans (Eq.symm ?_)
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Over.w v)).trans ?_)
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) (spMap_epsScale_comp_algebraMap c))
  have eact : ∀ (a : O) (v : epsPt x ⟶ G'), e (v ≫ act'.act a) = e v ≫ act.act a := by
    intro a v
    refine Over.OverMorphism.ext ?_
    rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, hact, Category.assoc]
  have eig : ∀ v : epsPt x ⟶ G', IsLieEigen act' x τ v ↔ IsLieEigen act (x ≫ f) τ (e v) := by
    intro v
    refine and_congr ?_ (forall_congr' fun a => by rw [scale, eact])
    rw [he, one, ← Category.assoc]
    refine ⟨fun hv => by rw [hv], fun hv => h.1.hom_ext hv ?_⟩
    refine Eq.trans ?_ (Over.w (1 : Over.mk x ⟶ G')).symm
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Over.w v)).trans ?_)
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ x) spMap_fstHom_comp_algebraMap).trans (Category.id_comp _))
  have prod : ∀ u : Fin n → (epsPt x ⟶ G'), e (List.ofFn u).prod = (List.ofFn fun i => e (u i)).prod := by
    intro u
    rw [map_list_prod, List.map_ofFn]
    rfl
  have key : ∀ (v : Fin n → (epsPt x ⟶ G')) (w : epsPt x ⟶ G') (c : Fin n → k),
      (∃ u : Fin n → (epsPt x ⟶ G'),
        (∀ i, (u i).left = spMap (epsScale (c i)) ≫ (v i).left) ∧ w = (List.ofFn u).prod) ↔
      ∃ u : Fin n → (epsPt (x ≫ f) ⟶ G),
        (∀ i, (u i).left = spMap (epsScale (c i)) ≫ (e (v i)).left) ∧ e w = (List.ofFn u).prod := by
    intro v w c
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun i => e (u i), fun i => (scale _ _ _).1 (hu i), prod u⟩
    · rintro ⟨u, hu, hw⟩
      refine ⟨fun i => e.symm (u i), fun i => (scale _ _ _).2 ?_, e.injective ?_⟩
      · rw [e.apply_symm_apply]; exact hu i
      · rw [prod, hw]
        simp only [e.apply_symm_apply]
  constructor
  · rintro ⟨v, hv, hw⟩
    refine ⟨fun i => e (v i), fun i => (eig _).1 (hv i), fun w hw' => ?_⟩
    obtain ⟨w, rfl⟩ := e.surjective w
    exact (existsUnique_congr (key v w)).1 (hw w ((eig w).2 hw'))
  · rintro ⟨v, hv, hw⟩
    obtain ⟨v, rfl⟩ : ∃ v' : Fin n → (epsPt x ⟶ G'), v = fun i => e (v' i) :=
      ⟨fun i => e.symm (v i), funext fun i => (e.apply_symm_apply _).symm⟩
    exact ⟨v, fun i => (eig _).2 (hv i), fun w hw' => (existsUnique_congr (key v w)).2 (hw _ ((eig w).1 hw'))⟩
end GlobalTheory
