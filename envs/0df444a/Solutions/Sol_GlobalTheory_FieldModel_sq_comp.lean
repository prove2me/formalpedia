-- Prove2me | solution 1 for GlobalTheory.FieldModel.sq_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:02:54.190321+00:00
-- url     : https://prove2.me/submissions/dfaf3b43-7f6c-497c-a487-55ce4afea7fd

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
theorem _root_.solution {S₁ : Scheme.{0}} {a : S₁ ⟶ S₀} {b : S ⟶ S₁} {B₁ : Over S₁} {ψ : B.left ⟶ B₁.left}
    {χ : B₁.left ⟶ B₀.left} (e : ψ ≫ χ = φ) (w : φ ≫ B₀.hom = B.hom ≫ c) (w₁ : ψ ≫ B₁.hom = B.hom ≫ b)
    (w₂ : χ ≫ B₀.hom = B₁.hom ≫ a) : sq w₁ ≫ sq w₂ = sq w := by
  apply Over.tensorObj_ext
  · change _ ≫ (fst B₀ B₀).left = _ ≫ (fst B₀ B₀).left
    rw [Category.assoc, sq_fst, sq_fst_assoc, sq_fst, e]
  · change _ ≫ (snd B₀ B₀).left = _ ≫ (snd B₀ B₀).left
    rw [Category.assoc, sq_snd, sq_snd_assoc, sq_snd, e]
end GlobalTheory.FieldModel
