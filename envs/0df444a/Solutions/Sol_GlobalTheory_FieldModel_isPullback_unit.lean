-- Prove2me | solution 1 for GlobalTheory.FieldModel.isPullback_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:00:17.245746+00:00
-- url     : https://prove2.me/submissions/80d06ca9-8e8b-4e60-acab-26140ffbf6cc

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
theorem _root_.solution (c : S ⟶ S₀) : IsPullback (show (𝟙_ (Over S)).left ⟶ (𝟙_ (Over S₀)).left from c)
    (𝟙_ (Over S)).hom (𝟙_ (Over S₀)).hom c :=
  IsPullback.of_vert_isIso (fst := c) (snd := 𝟙 S) (f := 𝟙 S₀) (g := c) ⟨by simp⟩
end GlobalTheory.FieldModel
