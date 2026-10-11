-- Prove2me | solution 1 for MazurTransfer.picard_pullback_isIso_of_curve_iso
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-10T16:04:24.514107+00:00
-- url     : https://prove2.me/submissions/c8445a29-6647-4284-81cf-22affe5aac6f

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Uses the checked complete original Anthropic FLT Picard inverse-pair
construction at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: any represented Picard morphism classifying re-rigidified
pullback by a curve isomorphism is itself a scheme isomorphism. The chosen
section may move. Named downstream consumer: the literal order-13 diamond
Picard group automorphism over Q and its scheme endomorphism norm descent.
-/
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_inverse_pair_of_iso_of_sections
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian

theorem solution {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (e : C ≅ C) (he : e.hom ≫ c = c) (he' : e.inv ≫ c = c)
    (N : SchemeHomOver D.toBase D.toBase)
    (hN : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase),
      Nonempty ((h.poincare.pullbackAlong (postComp N a)).L ≅
        Scheme.Modules.rigidify (rigSection c t ε) (pullback.snd c t)
          ((Scheme.Modules.pullback (curveChange e.inv he' t)).obj (h.poincare.pullbackAlong a).L))) :
    IsIso N.1 := by
  obtain ⟨θ, θ', hθ, hθ', hclass⟩ :=
    RepresentsRelSubPic.exists_inverse_pair_of_iso_of_sections ε ε e he he' h h
  let E : D.P ≅ D.P := ⟨θ.1, θ'.1, hθ, hθ'⟩
  have Hhom : E.hom = N.1 := by
    let t := D.toBase
    let a : SchemeHomOver t D.toBase := ⟨𝟙 _, Category.id_comp _⟩
    let b := postComp N a
    let M := h.poincare.pullbackAlong a
    let M' := h.poincare.pullbackAlong b
    have hP : FibrewiseAlgEquivZero h.poincare := h.poincare_mem
    have hM : FibrewiseAlgEquivZero M := hP.pullback a
    have hM' : FibrewiseAlgEquivZero M' := hP.pullback b
    let L := (Scheme.Modules.pullback (curveChange e.inv he' t)).obj M.L
    let Q := Scheme.Modules.dual ((Scheme.Modules.pullback (rigSection c t ε)).obj L)
    have hL : Scheme.Modules.IsInvertible L := M.isInvertible.pullback _
    have hQ : Scheme.Modules.IsInvertible Q := ((hL.pullback _).dual).1
    have H := hclass t M hM M' hM' Q hQ (hN t a)
    have ha : a = h.classify t M hM := h.classify_unique t M hM a ⟨Iso.refl _⟩
    have hb : b = h.classify t M' hM' := h.classify_unique t M' hM' b ⟨Iso.refl _⟩
    rw [← ha, ← hb] at H
    have Hv := congrArg Subtype.val H
    change 𝟙 _ ≫ E.hom = 𝟙 _ ≫ N.1 at Hv
    exact (Category.id_comp E.hom).symm.trans (Hv.trans (Category.id_comp N.1))
  rw [← Hhom]
  exact Iso.isIso_hom E

#print axioms solution
