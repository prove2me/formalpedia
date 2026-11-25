-- Prove2me | solution 1 for GlobalTheory.T.hasLocalisationAtElements_trivSqZeroExtForms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:50:47.875556+00:00
-- url     : https://prove2.me/submissions/f71066ff-3a26-4239-8cef-7961990c652d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasLocalisationAtElementsTrivSqZeroExtForms
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocalizationOfData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitMpOmjExtIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasLocalisationAtElementsTrivSqZeroExtFormsStatement
import Theorems.Thm_GlobalTheory_CechDR_FormExtJ_hasLoc_omjExt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (j : ℕ), Desc.HasLoc F → Desc.HasLoc (FormExtJ.omjExt F j) := by
  first | exact @GlobalTheory.CechDR.FormExtJ.hasLoc_omjExt | exact GlobalTheory.CechDR.FormExtJ.hasLoc_omjExt | (intros; apply GlobalTheory.CechDR.FormExtJ.hasLoc_omjExt <;> assumption)
end _root_.GlobalTheory.T
