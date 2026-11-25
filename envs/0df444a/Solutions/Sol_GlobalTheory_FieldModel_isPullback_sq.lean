-- Prove2me | solution 1 for GlobalTheory.FieldModel.isPullback_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:56:08.781444+00:00
-- url     : https://prove2.me/submissions/8123028c-ae67-4267-9021-3cad7b7e144a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomDescendsToSubfieldContainingFinsetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFinsetModelOfIsAffineStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GroupSchemeMorphismDescendsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusExtensionDescendsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFiniteTorusExtensionOfModel
import Theorems.Thm_GlobalTheory_FieldModel_sq_fst
import Theorems.Thm_GlobalTheory_FieldModel_sq_snd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [reassoc] GlobalTheory.FieldModel.sq_fst
attribute [reassoc] GlobalTheory.FieldModel.sq_snd

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.FieldModel
variable {K : Type} [Field K]
variable {S S₀ : Scheme.{0}} {c : S ⟶ S₀} {B : Over S} {B₀ : Over S₀} {φ : B.left ⟶ B₀.left}
namespace GlobalTheory.FieldModel
theorem _root_.solution (H : IsPullback φ B.hom B₀.hom c) :
    IsPullback (sq H.w) (B ⊗ B).hom (B₀ ⊗ B₀).hom c := by
  have h : IsPullback (fst B B).left (snd B B).left B.hom B.hom := .of_hasPullback _ _
  have h₀ : IsPullback (fst B₀ B₀).left (snd B₀ B₀).left B₀.hom B₀.hom := .of_hasPullback _ _
  have h₁ : IsPullback (sq H.w) (snd B B).left (snd B₀ B₀).left φ := by
    refine IsPullback.of_right ?_ (sq_snd _) h₀
    rw [sq_fst, H.w]
    exact h.paste_horiz H
  rw [← Over.w (snd B B), ← Over.w (snd B₀ B₀)]
  exact h₁.paste_vert H
end GlobalTheory.FieldModel
