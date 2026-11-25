-- Prove2me | solution 1 for GlobalTheory.T.charZero_stalk_imageOfGenericPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:12:18.599194+00:00
-- url     : https://prove2.me/submissions/fe58fbee-83d9-40e3-93d0-0a672858fbdb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CharZeroStalkImageOfGenericPoint
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FamIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CharZeroStalkImageOfGenericPointStatement
import Theorems.Thm_GlobalTheory_NormSheafDescent_charZero_stalk_genPt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsIntegral Y], CharZero Γ(Y, ⊤) →
    ∀ (hK : IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π))),
    letI := GlobalTheory.NormSheafDescent.fieldK π hK
    CharZero (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) := by
  first | exact @GlobalTheory.NormSheafDescent.charZero_stalk_genPt | exact GlobalTheory.NormSheafDescent.charZero_stalk_genPt | (intros; apply GlobalTheory.NormSheafDescent.charZero_stalk_genPt <;> assumption)
end _root_.GlobalTheory.T
