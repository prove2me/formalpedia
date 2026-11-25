-- Prove2me | solution 1 for GlobalTheory.GenericHom.exists_monHom_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:44:41.136516+00:00
-- url     : https://prove2.me/submissions/33d08be2-90ae-4584-858c-b1f97d075e51

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsMonHomExtension
import Theorems.Thm_GlobalTheory_GenericHom_mul_eq_of_generic
import Theorems.Thm_GlobalTheory_GenericHom_mul_four_eq_of_generic
import Theorems.Thm_GlobalTheory_GenericHom_exists_point_mem
import Theorems.Thm_GlobalTheory_GenericHom_hom_ext_points
import Theorems.Thm_GlobalTheory_GenericHom_exists_generic
import Theorems.Thm_GlobalTheory_GenericHom_point_comp_mul
import Theorems.Thm_GlobalTheory_isIntegral_of_smooth_of_geometricallyConnected


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.GenericHom
variable {k : Type} [Field k] [IsAlgClosed k]
namespace GlobalTheory.GenericHom
theorem _root_.solution : ∀ (k : Type) [Field k] [IsAlgClosed k] (H G U : Over (Sp k)) [GrpObj H] [GrpObj G], SmConn H → SmConn G → ∀ (j : U ⟶ H) (f : U ⟶ G), IsOpenImmersion j.left → Nonempty U.left → (∀ x y z : (𝟙_ (Over (Sp k)) ⟶ U), (x ≫ j) * (y ≫ j) = z ≫ j → (x ≫ f) * (y ≫ f) = z ≫ f) → ∃ F : H ⟶ G, IsMonHom F ∧ j ≫ F = f := by
  intro k _ _ H G U _ _ ⟨hc, hs, _, _, hgc⟩ ⟨_, _, _, _, _⟩ j f hj hU hm
  have : IsIntegral H.left := isIntegral_of_smooth_of_geometricallyConnected H.hom
  have htr : ∀ (a x : 𝟙_ (Over (Sp k)) ⟶ H), x ≫ (transl a).hom = a * x := fun a x =>
    (point_comp_mul x a (𝟙 H)).trans (by rw [Category.comp_id])
  have hg : ∀ s : List (𝟙_ (Over (Sp k)) ⟶ H), ∃ u, ∀ h ∈ s,
      ∃ p : 𝟙_ (Over (Sp k)) ⟶ U, p ≫ j = h * u := by
    intro s
    obtain ⟨u, hu⟩ := exists_generic j (s.map transl)
    exact ⟨u, fun h hh => htr h u ▸ hu _ (List.mem_map_of_mem hh)⟩
  have hdec : ∀ h : 𝟙_ (Over (Sp k)) ⟶ H, ∃ a x : 𝟙_ (Over (Sp k)) ⟶ U,
      (a ≫ j) * (x ≫ j) = h := by
    intro h
    obtain ⟨u, hu⟩ := exists_generic j [Iso.refl H, asIso (ι[H]) ≪≫ transl h]
    obtain ⟨x, hx⟩ := hu (Iso.refl H) (by simp)
    obtain ⟨a, ha⟩ := hu (asIso (ι[H]) ≪≫ transl h) (by simp)
    refine ⟨a, x, ?_⟩
    rw [ha, hx, Iso.trans_hom, ← Category.assoc, htr, asIso_hom, Iso.refl_hom, Category.comp_id,
      ← Hom.inv_def, inv_mul_cancel_right]
  let J : (𝟙_ (Over (Sp k)) ⟶ U) → (U ⟶ H) := fun a => j ≫ (transl (a ≫ j)).hom
  let φ : (𝟙_ (Over (Sp k)) ⟶ U) → (U ⟶ G) := fun a => (toUnit U ≫ a ≫ f) * f
  have hJ : ∀ a x : 𝟙_ (Over (Sp k)) ⟶ U, x ≫ J a = (a ≫ j) * (x ≫ j) := fun a x => by
    rw [← htr, Category.assoc]
  have hφ : ∀ a x : 𝟙_ (Over (Sp k)) ⟶ U, x ≫ φ a = (a ≫ f) * (x ≫ f) := fun a x =>
    point_comp_mul x _ _
  have hJo : ∀ a, IsOpenImmersion (J a).left := fun a => by
    have : IsIso (transl (a ≫ j)).hom.left :=
      inferInstanceAs (IsIso ((Over.forget _).map (transl (a ≫ j)).hom))
    exact inferInstanceAs (IsOpenImmersion (j.left ≫ (transl (a ≫ j)).hom.left))
  have hcov : ∀ y : H.left, ∃ a, y ∈ Set.range (J a).left := by
    by_contra hn
    push Not at hn
    obtain ⟨y, hy⟩ := hn
    have hcl : IsClosed (⋃ a, Set.range (J a).left)ᶜ :=
      (isOpen_iUnion fun a => IsOpenImmersion.isOpen_range (J a).left).isClosed_compl
    obtain ⟨h, hh⟩ := exists_point_mem H _ hcl.isLocallyClosed ⟨y, by simpa using hy⟩
    obtain ⟨a, x, e⟩ := hdec h
    rw [← hJ] at e
    subst e
    exact hh (IsLocalRing.closedPoint k) (Set.mem_iUnion.2 ⟨a, x.left (IsLocalRing.closedPoint k), rfl⟩)
  have hsU : Smooth U.hom := by rw [← Over.w j]; infer_instance
  let 𝒰 : H.left.OpenCover := Scheme.Cover.mkOfCovers (𝟙_ (Over (Sp k)) ⟶ U) (fun _ => U.left)
    (fun a => (J a).left) (fun y => hcov y) hJo
  have hcomp : ∀ a b, pullback.fst (J a).left (J b).left ≫ (φ a).left =
      pullback.snd (J a).left (J b).left ≫ (φ b).left := by
    intro a b
    let Z : Over (Sp k) := Over.mk (pullback.fst (J a).left (J b).left ≫ U.hom)
    have : Smooth Z.hom := inferInstanceAs (Smooth (pullback.fst (J a).left (J b).left ≫ U.hom))
    let p₁ : Z ⟶ U := Over.homMk (pullback.fst (J a).left (J b).left) rfl
    let p₂ : Z ⟶ U := Over.homMk (pullback.snd (J a).left (J b).left) (by
      show _ = pullback.fst (J a).left (J b).left ≫ U.hom
      have e := congrArg (· ≫ H.hom) (pullback.condition (f := (J a).left) (g := (J b).left))
      simp only [Category.assoc, Over.w] at e
      exact e.symm)
    have hp : p₁ ≫ J a = p₂ ≫ J b := Over.OverMorphism.ext pullback.condition
    have : p₁ ≫ φ a = p₂ ≫ φ b := hom_ext_points _ _ fun z => by
      rw [← Category.assoc, ← Category.assoc, hφ, hφ]
      refine mul_eq_of_generic (· ≫ j) (· ≫ f) hm hg _ _ _ _ ?_
      show (a ≫ j) * ((z ≫ p₁) ≫ j) = (b ≫ j) * ((z ≫ p₂) ≫ j)
      rw [← hJ, ← hJ, Category.assoc, Category.assoc, hp]
    exact congrArg CommaMorphism.left this
  let F₀ : H.left ⟶ G.left := 𝒰.glueMorphisms (fun a => (φ a).left) hcomp
  have hF₀ : ∀ a, (J a).left ≫ F₀ = (φ a).left := fun a =>
    𝒰.ι_glueMorphisms (fun a => (φ a).left) hcomp a
  let F : H ⟶ G := Over.homMk F₀ (𝒰.hom_ext _ _ fun a => by
    show (J a).left ≫ F₀ ≫ G.hom = (J a).left ≫ H.hom
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ G.hom) (hF₀ a)).trans
      ((Over.w (φ a)).trans (Over.w (J a)).symm)))
  have hF : ∀ a x : 𝟙_ (Over (Sp k)) ⟶ U, ((a ≫ j) * (x ≫ j)) ≫ F = (a ≫ f) * (x ≫ f) := by
    intro a x
    have : J a ≫ F = φ a := Over.OverMorphism.ext (hF₀ a)
    rw [← hJ, Category.assoc, this, hφ]
  have hmul : ∀ h h' : 𝟙_ (Over (Sp k)) ⟶ H, (h * h') ≫ F = (h ≫ F) * (h' ≫ F) := by
    intro h h'
    obtain ⟨c, z, e⟩ := hdec (h * h')
    obtain ⟨a, x, rfl⟩ := hdec h
    obtain ⟨b, y, rfl⟩ := hdec h'
    rw [← e, hF, hF, hF]
    exact (mul_four_eq_of_generic (· ≫ j) (· ≫ f) hm hg _ _ _ _ _ _ e.symm).symm
  refine ⟨F, ⟨?_, ?_⟩, hom_ext_points _ _ fun w => ?_⟩
  · have := hmul 1 1
    rw [_root_.one_mul] at this
    have h1 : (1 : 𝟙_ (Over (Sp k)) ⟶ H) ≫ F = 1 := left_eq_mul.1 this
    simpa [Hom.one_def] using h1
  · have : Smooth (H ⊗ H).hom := inferInstanceAs (Smooth (pullback.fst H.hom H.hom ≫ H.hom))
    refine hom_ext_points _ _ fun z => ?_
    have := hmul (z ≫ fst H H) (z ≫ snd H H)
    rw [Hom.mul_def, Hom.mul_def, lift_comp_fst_snd] at this
    rw [← Category.assoc, this, ← Category.assoc]
    congr 1
    ext <;> simp
  · obtain ⟨a, x, e⟩ := hdec (w ≫ j)
    rw [← Category.assoc, ← e, hF]
    exact hm _ _ _ e
end GlobalTheory.GenericHom
