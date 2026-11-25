-- Prove2me | solution 1 for GlobalTheory.T.isMonHom_pointed_splitExt_to_abelianVariety
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:52:49.552824+00:00
-- url     : https://prove2.me/submissions/1c5a888e-44ae-42f9-a51b-ec65dfd9032b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsMonHomPointedSplitExtToAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsMonHomPointedSplitExtToAbelianVarietyStatement
import Theorems.Thm_GlobalTheory_ExtensionRigidity_isMonHom_of_pointed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [IsAlgClosed K] (E : SplitExt (Sp K)) (G : Over (Sp K)) [GrpObj G], E.IsGt G → ∀ (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ f : G ⟶ B, η[G] ≫ f = η[B] → IsMonHom f := by
  first | exact @GlobalTheory.ExtensionRigidity.isMonHom_of_pointed | exact GlobalTheory.ExtensionRigidity.isMonHom_of_pointed | (intros; apply GlobalTheory.ExtensionRigidity.isMonHom_of_pointed <;> assumption)
end _root_.GlobalTheory.T
