-- Prove2me | solution 1 for GlobalTheory.ClosedLimit.exists_isClosedImmersion_of_isLimit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:42:14.642856+00:00
-- url     : https://prove2.me/submissions/67f7a50f-c3de-44e5-bade-928187483922

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KaRuleK
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsClosedImmersionDescendsToSubring
import Theorems.Thm_GlobalTheory_ClosedLimit_surjective_of_isPushout
import Theorems.Thm_GlobalTheory_KeyPow_ClauseH_mono
import Theorems.Thm_GlobalTheory_KeyPow_KeyRule_mono
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.ClosedLimit
universe u
namespace GlobalTheory.ClosedLimit
theorem _root_.solution {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D E : I ⥤ Scheme.{u}) (α : D ⟶ E) (c : Cone D) (d : Cone E) (hc : IsLimit c) (hd : IsLimit d)
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ {i j} (f : i ⟶ j), IsAffineHom (E.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] [∀ i, IsAffine (E.obj i)]
    [∀ i, LocallyOfFiniteType (α.app i)]
    (hα : ∀ {i j} (f : i ⟶ j), IsPullback (D.map f) (α.app i) (α.app j) (E.map f))
    (g : c.pt ⟶ d.pt) [IsClosedImmersion g] (hg : ∀ i, g ≫ d.π.app i = c.π.app i ≫ α.app i) :
    ∃ i, IsClosedImmersion (α.app i) := by
  classical
  have : IsAffine d.pt := Scheme.isAffine_of_isLimit _ hd
  obtain ⟨_, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine g
  obtain ⟨i, hi⟩ := Scheme.exists_isAffine_of_isLimit D c hc
  have one (x : Γ(D.obj i, ⊤)) : ∃ (j : I) (f : j ⟶ i),
      (D.map f).appTop.hom x ∈ (α.app j).appTop.hom.range := by
    obtain ⟨y, hy⟩ := hsurj ((c.π.app i).appTop x)
    obtain ⟨j, y, rfl⟩ := exists_appTop_π_eq_of_isAffine_of_isLimit E d hd y
    let m := IsCofiltered.min i j
    let a : m ⟶ i := IsCofiltered.minToLeft i j
    let b : m ⟶ j := IsCofiltered.minToRight i j
    have e₁ : c.π.app m ≫ D.map a = c.π.app i := c.w a
    have e₂ : c.π.app m ≫ α.app m ≫ E.map b = g ≫ d.π.app j := by
      rw [← reassoc_of% hg, d.w b]
    obtain ⟨l, f, hl⟩ := exists_app_map_eq_map_of_isLimit D c hc (U := ⊤) isCompact_univ
      ((D.map a).appTop x) ((α.app m ≫ E.map b).appTop y) (by
        have h₁ : (c.π.app m).appTop ((D.map a).appTop x) = (c.π.app i).appTop x :=
          congr(($e₁).appTop x)
        have h₂ : (c.π.app m).appTop ((α.app m ≫ E.map b).appTop y) =
          g.appTop ((d.π.app j).appTop y) := congr(($e₂).appTop y)
        exact h₁.trans (hy.symm.trans h₂.symm))
    refine ⟨l, f ≫ a, (E.map f ≫ E.map b).appTop y, ?_⟩
    have e₃ : α.app l ≫ E.map f ≫ E.map b = D.map f ≫ α.app m ≫ E.map b := by
      rw [α.naturality_assoc]
    have h₃ : (α.app l).appTop ((E.map f ≫ E.map b).appTop y) =
      (D.map f).appTop ((α.app m ≫ E.map b).appTop y) := congr(($e₃).appTop y)
    have h₄ : (D.map (f ≫ a)).appTop x = (D.map f).appTop ((D.map a).appTop x) :=
      congr(($(D.map_comp f a)).appTop x)
    exact h₃.trans (hl.symm.trans h₄.symm)
  have mono {j l : I} (f : j ⟶ i) (h : l ⟶ j) (x : Γ(D.obj i, ⊤))
      (hx : (D.map f).appTop.hom x ∈ (α.app j).appTop.hom.range) :
      (D.map (h ≫ f)).appTop.hom x ∈ (α.app l).appTop.hom.range := by
    obtain ⟨y, hy⟩ := hx
    refine ⟨(E.map h).appTop y, ?_⟩
    have h₃ : (α.app l).appTop ((E.map h).appTop y) =
      (D.map h).appTop ((α.app j).appTop y) := congr(($((α.naturality h).symm)).appTop y)
    have h₄ : (D.map (h ≫ f)).appTop x = (D.map h).appTop ((D.map f).appTop x) :=
      congr(($(D.map_comp h f)).appTop x)
    exact h₃.trans ((congrArg _ hy).trans h₄.symm)
  have many (s : Finset Γ(D.obj i, ⊤)) : ∃ (j : I) (f : j ⟶ i), ∀ x ∈ s,
      (D.map f).appTop.hom x ∈ (α.app j).appTop.hom.range := by
    induction s using Finset.induction_on with
    | empty => exact ⟨i, 𝟙 i, by simp⟩
    | insert x s _ ih =>
      obtain ⟨j₁, f₁, h₁⟩ := ih
      obtain ⟨j₂, f₂, h₂⟩ := one x
      obtain ⟨l, g₁, g₂, eg⟩ := IsCofiltered.cospan f₁ f₂
      refine ⟨l, g₁ ≫ f₁, fun y hy ↦ ?_⟩
      rcases Finset.mem_insert.mp hy with rfl | hy
      · rw [eg]; exact mono _ _ _ h₂
      · exact mono _ _ _ (h₁ y hy)
  have hft : (α.app i).appTop.hom.FiniteType :=
    HasRingHomProperty.appTop (P := @LocallyOfFiniteType) _ inferInstance
  let _ := (α.app i).appTop.hom.toAlgebra
  obtain ⟨s, hs⟩ := hft.out
  obtain ⟨j, f, hj⟩ := many s
  have : IsAffine (D.obj j) := isAffine_of_isAffineHom (D.map f)
  refine ⟨j, IsClosedImmersion.of_surjective_of_isAffine _ ?_⟩
  refine surjective_of_isPushout (isPushout_appTop_of_isPullback (hα f)) s ?_ hj
  exact (Algebra.adjoin_eq_ring_closure (s : Set Γ(D.obj i, ⊤))).symm.trans (congrArg Subalgebra.toSubring hs)
end GlobalTheory.ClosedLimit
