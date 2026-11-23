-- Prove2me | solution 1 for GlobalTheory.FrameBasic.sig_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:53:03.822801+00:00
-- url     : https://prove2.me/submissions/10c20a99-c5d7-415c-97b6-8f01751834b4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical TensorProduct
open GlobalTheory GlobalTheory.FrameBasic
variable {E : Type} [CommRing E]
namespace GlobalTheory.FrameBasic
theorem _root_.solution (t : Eˣ) (s : ℕ+) (bs : List (Eˣ × ℕ+)) (a : ℕ) :
    sig ((t, s) :: bs) a = if a < s then s - 1 - a else s + sig bs (a - s) := rfl
end GlobalTheory.FrameBasic
