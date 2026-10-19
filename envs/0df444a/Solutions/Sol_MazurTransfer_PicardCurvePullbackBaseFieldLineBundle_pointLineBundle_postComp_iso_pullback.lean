-- Prove2me | solution 1 for MazurTransfer.PicardCurvePullbackBaseFieldLineBundle.pointLineBundle_postComp_iso_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T12:33:35.551058+00:00
-- url     : https://prove2.me/submissions/1f21ed89-9bee-4ba0-ad7d-3b18fd95c3a0

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: re-rigidified Picard pullback induces literal curve
pullback on the base-field point's line bundle. Named downstream consumer:
actual divisor presentation transport and arithmetic Pic0 naturality.
-/
import Definitions.Def_MazurTransfer_PicardReRigidifiedCurvePullbackData
import Definitions.Def_MazurTransfer_RepresentedPicardBaseFieldPointLineBundle
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field
noncomputable section
universe u
open MazurTransfer
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open PicardReRigidifiedCurvePullback LineBundleFieldComparison
variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
  (D : RelativePic0Designation K c)
  (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
  (f : C ⟶ C) (hf : f ≫ c = c)

namespace MazurTransfer.BaseFieldCurvePullbackHelpers20261017
theorem rigidify_iso_of_field (K : Type u) [Field K] {P : Scheme.{u}}
    (σ : Spec (CommRingCat.of K) ⟶ P) (q : P ⟶ Spec (CommRingCat.of K))
    (L : P.Modules) (hL : Scheme.Modules.IsInvertible L) :
    Nonempty (Scheme.Modules.rigidify σ q L ≅ L) := by
  have hQ : Scheme.Modules.IsInvertible (Scheme.Modules.dual ((Scheme.Modules.pullback σ).obj L)) :=
    (hL.pullback σ).dual.1
  obtain ⟨e⟩ := Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field K _ hQ
  exact ⟨(Iso.refl L ⊗ᵢ (Scheme.Modules.pullback q).mapIso e) ≪≫
    (Iso.refl L ⊗ᵢ Scheme.Modules.pullbackTensorUnitObjIso q) ≪≫ ρ_ L⟩

theorem toProdSpec_curveChange :
    toProdSpec c ≫ curveChange f hf (𝟙 _) = f ≫ toProdSpec c := by
  apply pullback.hom_ext
  · simp only [curveChange, toProdSpec, Category.assoc, pullback.map,
      pullback.lift_fst_assoc, pullback.lift_fst, Category.id_comp, Category.comp_id]
  · simp only [curveChange, toProdSpec, Category.assoc, pullback.map,
      pullback.lift_snd_assoc, pullback.lift_snd, Category.id_comp, Category.comp_id]
    exact hf.symm

end MazurTransfer.BaseFieldCurvePullbackHelpers20261017
open MazurTransfer.BaseFieldCurvePullbackHelpers20261017
theorem solution
    (N : PullbackData h f hf)
    (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase) :
    Nonempty (pointLineBundle c ε D h (postComp N.hom a) ≅
      (Scheme.Modules.pullback f).obj (pointLineBundle c ε D h a)) := by
  let L := (Scheme.Modules.pullback (curveChange f hf (𝟙 _))).obj (h.poincare.pullbackAlong a).L
  have hL : Scheme.Modules.IsInvertible L := (h.poincare.pullbackAlong a).isInvertible.pullback _
  obtain ⟨e₁⟩ := N.classifies (𝟙 _) a
  obtain ⟨e₂⟩ := MazurTransfer.BaseFieldCurvePullbackHelpers20261017.rigidify_iso_of_field K
    (rigSection c (𝟙 _) ε) (pullback.snd c (𝟙 _)) L hL
  exact ⟨(Scheme.Modules.pullback (toProdSpec c)).mapIso (e₁ ≪≫ e₂) ≪≫
    (Scheme.Modules.pullbackComp (toProdSpec c) (curveChange f hf (𝟙 _))).app (h.poincare.pullbackAlong a).L ≪≫
    (Scheme.Modules.pullbackCongr (toProdSpec_curveChange c f hf)).app (h.poincare.pullbackAlong a).L ≪≫
    ((Scheme.Modules.pullbackComp f (toProdSpec c)).app (h.poincare.pullbackAlong a).L).symm⟩

#print axioms solution
