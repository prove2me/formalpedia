-- Prove2me | solution 1 for GlobalTheory.T.rationalCommonStabiliser_eq_one_of_fixes_second_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:32:32.122189+00:00
-- url     : https://prove2.me/submissions/72276e77-8777-411e-9ae6-90026af4563e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalCommonStabiliserEqOneOfFixesSecondFrame
import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalCommonStabiliserEqOneOfFixesSecondFrameStatement
import Theorems.Thm_GlobalTheory_HL_StabFix_eq_one_of_fix


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ x ∈ G.St, (∀ b, x (G.f' b) = G.f' b) → x = 1 := by
  first | exact @GlobalTheory.HL.StabFix.eq_one_of_fix | exact GlobalTheory.HL.StabFix.eq_one_of_fix | (intros; apply GlobalTheory.HL.StabFix.eq_one_of_fix <;> assumption)
end _root_.GlobalTheory.T
