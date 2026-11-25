-- Prove2me | solution 1 for GlobalTheory.FieldModel.exists_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:35:15.7038+00:00
-- url     : https://prove2.me/submissions/b38a087d-a11a-42af-9e3e-a9e0d8690c94

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

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.FieldModel
namespace GlobalTheory.FieldModel
theorem _root_.solution {S S₁ S₀ : Scheme.{0}} {a : S₁ ⟶ S₀} {b : S ⟶ S₁} {c : S ⟶ S₀} (h : b ≫ a = c)
    {X : Over S} {X₀ : Over S₀} {φ : X.left ⟶ X₀.left} (H : IsPullback φ X.hom X₀.hom c) :
    ∃ φ₁ : X.left ⟶ ((Over.pullback a).obj X₀).left, φ₁ ≫ pullback.fst X₀.hom a = φ ∧
      IsPullback φ₁ X.hom ((Over.pullback a).obj X₀).hom b := by
  refine ⟨pullback.lift φ (X.hom ≫ b) (by rw [Category.assoc, h, H.w]), pullback.lift_fst _ _ _, ?_⟩
  refine IsPullback.of_right (h₁₂ := pullback.fst X₀.hom a) (v₁₃ := X₀.hom) (h₂₂ := a) ?_
    (pullback.lift_snd _ _ _) (.of_hasPullback _ _)
  rw [pullback.lift_fst, h]
  exact H
end GlobalTheory.FieldModel
