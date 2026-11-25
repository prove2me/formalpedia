-- Prove2me | solution 1 for GlobalTheory.FieldModel.HasModel.sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:48:30.255797+00:00
-- url     : https://prove2.me/submissions/1f28864f-d8d7-44ca-b4dd-6fe70222f37e

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
import Theorems.Thm_GlobalTheory_FieldModel_HasModel_glue

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
variable {K : Type} [Field K]
namespace GlobalTheory.FieldModel
namespace HasModel
theorem _root_.solution (X : Over (Sp K)) [LocallyOfFiniteType X.hom] [IsSeparated X.hom] (A B : X.left.Opens)
    (hc : IsCompact ((A ⊓ B : X.left.Opens) : Set X.left))
    (hA : HasModel (part X A)) (hB : HasModel (part X B)) (hAB : HasModel (part X (A ⊓ B))) :
    HasModel (part X (A ⊔ B)) := by
  have : CompactSpace (A ⊓ B : X.left.Opens).toScheme := isCompact_iff_compactSpace.1 hc
  refine HasModel.glue (partMap X le_sup_left) (partMap X le_sup_right) (partMap X inf_le_left)
    (partMap X inf_le_right) (inferInstanceAs (IsOpenImmersion (X.left.homOfLE le_sup_left)))
    (inferInstanceAs (IsOpenImmersion (X.left.homOfLE le_sup_right)))
    (isPullback_opens_inf_le le_sup_left le_sup_right) (fun x => ?_)
    (inferInstanceAs (QuasiCompact ((A ⊓ B).ι ≫ X.hom))) (inferInstanceAs (QuasiSeparated ((A ⊓ B).ι ≫ X.hom)))
    (inferInstanceAs (LocallyOfFiniteType (A.ι ≫ X.hom))) (inferInstanceAs (LocallyOfFiniteType (B.ι ≫ X.hom)))
    hA hB hAB
  obtain ⟨x, hx | hx⟩ := x
  · exact Or.inl ⟨⟨x, hx⟩, Subtype.ext (X.left.homOfLE_apply le_sup_left _)⟩
  · exact Or.inr ⟨⟨x, hx⟩, Subtype.ext (X.left.homOfLE_apply le_sup_right _)⟩
end HasModel
end GlobalTheory.FieldModel
