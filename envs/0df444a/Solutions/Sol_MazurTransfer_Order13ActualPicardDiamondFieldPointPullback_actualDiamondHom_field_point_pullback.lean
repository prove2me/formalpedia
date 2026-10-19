-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardDiamondFieldPointPullback.actualDiamondHom_field_point_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T11:46:48.335434+00:00
-- url     : https://prove2.me/submissions/391365dc-edad-407a-9b9e-96a4ff0db3ad

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Uses checked original Anthropic FLT invertible-sheaf triviality over a field
at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: on every field-valued Picard point, the actual diamond
scheme action pulls back the underlying line bundle by the inverse curve
automorphism; the rigidifying correction from the field base is trivial.
Named downstream consumer: comparison with actual arithmetic Pic0 transport.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardDiamondSchemeEndomorphism
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field
noncomputable section
open MazurTransfer
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualDiamondCurveAutomorphism Order13ActualPicardDiamondSchemeEndomorphism

namespace MazurTransfer.ActualPicardDiamondFieldPullbackHelpers20261017
theorem rigidify_iso_of_field.{u} (K : Type u) [Field K] {P : Scheme.{u}}
    (σ : Spec (CommRingCat.of K) ⟶ P) (q : P ⟶ Spec (CommRingCat.of K))
    (L : P.Modules) (hL : Scheme.Modules.IsInvertible L) :
    Nonempty (Scheme.Modules.rigidify σ q L ≅ L) := by
  have hQ : Scheme.Modules.IsInvertible (Scheme.Modules.dual ((Scheme.Modules.pullback σ).obj L)) :=
    (hL.pullback σ).dual.1
  obtain ⟨e⟩ := Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field K _ hQ
  exact ⟨(Iso.refl L ⊗ᵢ (Scheme.Modules.pullback q).mapIso e) ≪≫
    (Iso.refl L ⊗ᵢ Scheme.Modules.pullbackTensorUnitObjIso q) ≪≫ ρ_ L⟩

end MazurTransfer.ActualPicardDiamondFieldPullbackHelpers20261017
open MazurTransfer.ActualPicardDiamondFieldPullbackHelpers20261017
theorem solution (K : Type) [Field K]
    (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
    (a : SchemeHomOver t actualPicard.toBase) :
    Nonempty ((actualRepresentation.poincare.pullbackAlong (postComp actualDiamondHom a)).L ≅
      (Scheme.Modules.pullback (curveChange diamondCurveIso.inv diamondCurveIso_inv_over t)).obj
        (actualRepresentation.poincare.pullbackAlong a).L) := by
  let L := (Scheme.Modules.pullback (curveChange diamondCurveIso.inv diamondCurveIso_inv_over t)).obj
    (actualRepresentation.poincare.pullbackAlong a).L
  have hL : Scheme.Modules.IsInvertible L :=
    (actualRepresentation.poincare.pullbackAlong a).isInvertible.pullback _
  obtain ⟨e₁⟩ := actualDiamondAction.classifies t a
  obtain ⟨e₂⟩ := rigidify_iso_of_field K (rigSection (curveToBase ℚ) t infinitySection)
    (pullback.snd (curveToBase ℚ) t) L hL
  exact ⟨e₁ ≪≫ e₂⟩

#print axioms solution
