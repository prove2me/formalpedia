-- Prove2me | solution 1 for MazurTransfer.FieldDivisorComparison.nonempty_iso_tensorUnit_of_principal_presentation
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T19:28:11.817867+00:00
-- url     : https://prove2.me/submissions/90402671-7455-4852-ae4f-3664df1269c4

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
The affine-cover, section comparison and Cartier-divisor arguments reuse official
Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: a principal function-field presentation gives a nonzero global
section, and numerical degree zero then gives a trivial line bundle over the
actual base field. Named downstream consumer: the kernel of the order-13
arithmetic Picard-point map. No algebraic-closure hypothesis is imposed.
-/
import Definitions.Def_MazurTransfer_OriginalDivisorPresentationTransportDataExplicitSectionSpaces20261017
import Definitions.Def_MazurTransfer_LineBundleGeometricDegreeZeroData
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Theorems.Thm_MazurTransfer_LineBundleFieldComparison_nonempty_iso_tensorUnit_of_curveEulerChar_eq_of_ne_zero
import Theorems.Thm_AlgebraicCurve_nonempty_linearEquiv_cechH0_and_cechH1_sectionsOf_of_range_eq_lSpaceOn
import Theorems.Thm_AlgebraicCurve_placesOf_union_eq_univ_of_sup_eq_top
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import Theorems.Thm_AlgebraicGeometry_not_isAffine_of_isProper_of_smoothOfRelativeDimension_one
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve TopologicalSpace
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
open MazurTransfer.LineBundleFieldComparison
namespace MazurTransfer.PrincipalPresentationGlobalSectionHelpers20261017
noncomputable def sectionsOfGlobal {X : Scheme.{u}} (L : X.Modules) (m : Γ(L, ⊤)) : SheafOfModules.sections L :=
  PresheafOfModules.sectionsMk (M := L.val)
    (fun U => (L.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op m : Γ(L, U.unop)))
    (by
      intro U V f
      change (L.presheaf.map f) ((L.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op) m) =
        (L.presheaf.map (homOfLE (le_top : V.unop ≤ ⊤)).op) m
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      exact congrArg (fun g => (L.presheaf.map g) m) (Quiver.Hom.unop_inj (Subsingleton.elim _ _)))

theorem sectionsOfGlobal_top {X : Scheme.{u}} (L : X.Modules) (m : Γ(L, ⊤)) :
    (sectionsOfGlobal L m).1 (Opposite.op ⊤) = m := by
  change (L.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op) m = m
  have : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  rw [this, CategoryTheory.Functor.map_id]
  rfl


noncomputable def homOfGlobal {X : Scheme.{u}} (L : X.Modules) (m : Γ(L, ⊤)) : 𝟙_ X.Modules ⟶ L :=
  (SheafOfModules.unitHomEquiv L).symm (sectionsOfGlobal L m)

theorem app_homOfGlobal_one {X : Scheme.{u}} (L : X.Modules) (m : Γ(L, ⊤)) :
    (Scheme.Modules.Hom.app (homOfGlobal L m) ⊤) (Scheme.Modules.toUnitSection ⊤ 1) = m := by
  have h1 := SheafOfModules.unitHomEquiv_apply_coe L (homOfGlobal L m) (Opposite.op ⊤)
  rw [homOfGlobal, Equiv.apply_symm_apply, sectionsOfGlobal_top] at h1
  exact h1.symm

theorem homOfGlobal_ne_zero {X : Scheme.{u}} (L : X.Modules) {m : Γ(L, ⊤)} (hm : m ≠ 0) :
    homOfGlobal L m ≠ 0 := by
  intro h0
  apply hm
  have h1 := app_homOfGlobal_one L m
  rw [h0, Scheme.Modules.Hom.zero_app] at h1
  exact h1.symm.trans (AddCommGrpCat.zero_apply _ _ _)


theorem exists_hom_ne_zero_of_nontrivial_H0 {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (𝒱 : X.TwoAffineOpenCover) (L : X.Modules) (hL : Nontrivial (𝒱.sectionsOf x L).H0) :
    ∃ s : 𝟙_ X.Modules ⟶ L, s ≠ 0 := by
  obtain ⟨e, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 𝒱 x L
  haveI : Nontrivial Γ(L, ⊤) := e.toEquiv.nontrivial
  obtain ⟨m, hm⟩ := exists_ne (0 : Γ(L, ⊤))
  exact ⟨homOfGlobal L m, homOfGlobal_ne_zero L hm⟩


end MazurTransfer.PrincipalPresentationGlobalSectionHelpers20261017
open MazurTransfer.PrincipalPresentationGlobalSectionHelpers20261017
private theorem affineOpen_ne_top {X : Scheme.{u}} (hX : ¬ IsAffine X) {U : X.Opens}
    (hU : IsAffineOpen U) : U ≠ ⊤ := by
  intro h
  apply hX
  have hT : IsAffineOpen (⊤ : X.Opens) := h ▸ hU
  haveI : IsAffine (⊤ : X.Opens) := hT
  exact IsAffine.of_isIso X.topIso.inv

theorem solution
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    (x : X ⟶ Spec (CommRingCat.of K))
    [IsProper x] [SmoothOfRelativeDimension 1 x] [GeometricallyIrreducible x]
    (𝒱 : X.TwoAffineOpenCover) (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    (hχ : curveEulerChar x 𝒱 M = curveEulerChar x 𝒱 (𝟙_ X.Modules))
    (E : letI := (baseToFunctionField x).toAlgebra; Divisor K X.functionField)
    (φ : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u))
    (hp : IsPresentation x M E φ)
    (hE : letI := (baseToFunctionField x).toAlgebra; Divisor.IsPrincipal E) :
    Nonempty (M ≅ 𝟙_ X.Modules) := by
  letI := (baseToFunctionField x).toAlgebra
  have hNA := not_isAffine_of_isProper_of_smoothOfRelativeDimension_one x
  have hne0 : 𝒱.U0 ≠ ⊤ := affineOpen_ne_top hNA 𝒱.isAffineOpen_U0
  have hne1 : 𝒱.U1 ≠ ⊤ := affineOpen_ne_top hNA 𝒱.isAffineOpen_U1
  have h0 : Nonempty 𝒱.U0 := by
    by_contra hc
    apply hne1
    have hb : 𝒱.U0 = ⊥ := by
      ext z
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hz => hc ⟨⟨z, hz⟩⟩
    have := 𝒱.sup_eq_top
    rwa [hb, bot_sup_eq] at this
  have h1 : Nonempty 𝒱.U1 := by
    by_contra hc
    apply hne0
    have hb : 𝒱.U1 = ⊥ := by
      ext z
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hz => hc ⟨⟨z, hz⟩⟩
    have := 𝒱.sup_eq_top
    rwa [hb, sup_bot_eq] at this
  obtain ⟨hcov, hS0, hS1⟩ :=
    placesOf_union_eq_univ_of_sup_eq_top x 𝒱.U0 𝒱.U1 𝒱.sup_eq_top hne0 hne1
  obtain ⟨⟨e0⟩, -⟩ :=
    nonempty_linearEquiv_cechH0_and_cechH1_sectionsOf_of_range_eq_lSpaceOn
      𝒱 x h0 h1 M E φ hp.nat (fun U _ a m => hp.smul U a m) hp.inj hp.range
  obtain ⟨f, hf, hEf⟩ := hE
  have hfL : f⁻¹ ∈ LSpace E := by
    apply mem_lSpace_iff_ord.mpr
    right
    intro v
    rw [v.ord_inv, hEf v]
  haveI : Nontrivial (LSpace E) :=
    ⟨⟨⟨f⁻¹, hfL⟩, 0, fun h => inv_ne_zero hf (congrArg Subtype.val h)⟩⟩
  haveI : Nontrivial (𝒱.sectionsOf x M).H0 :=
    (e0.trans (cechH0Equiv hcov E)).toEquiv.nontrivial
  obtain ⟨s, hs⟩ := exists_hom_ne_zero_of_nontrivial_H0 x 𝒱 M inferInstance
  exact nonempty_iso_tensorUnit_of_curveEulerChar_eq_of_ne_zero x 𝒱 hM hχ s hs


#print axioms solution
