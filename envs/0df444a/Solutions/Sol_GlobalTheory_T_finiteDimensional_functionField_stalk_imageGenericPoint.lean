-- Prove2me | solution 1 for GlobalTheory.T.finiteDimensional_functionField_stalk_imageGenericPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:20:59.596436+00:00
-- url     : https://prove2.me/submissions/8d17af1c-28d0-43a1-bb2c-c5611061526f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalFunctionFieldStalkImageGenericP
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FamIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalFunctionFieldStalkImageGenericPStatement
import Theorems.Thm_GlobalTheory_NormSheafDescent_finiteDimensional_functionField


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
theorem _root_.solution : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsFinite π] [IsIntegral Y]
    (hK : IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π))),
    letI := GlobalTheory.NormSheafDescent.fieldK π hK; letI := GlobalTheory.NormSheafDescent.algKL π
    FiniteDimensional (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) Y.functionField := by
  first | exact @GlobalTheory.NormSheafDescent.finiteDimensional_functionField | exact GlobalTheory.NormSheafDescent.finiteDimensional_functionField | (intros; apply GlobalTheory.NormSheafDescent.finiteDimensional_functionField <;> assumption)
end _root_.GlobalTheory.T
