-- Prove2me | solution 1 for GlobalTheory.T.rationalPairingMatrix_inv_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:59:21.869207+00:00
-- url     : https://prove2.me/submissions/19e8f33e-a618-4a95-af56-68303a7a359b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalPairingMatrixInvMulSelf
import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalPairingMatrixInvMulSelfStatement
import Theorems.Thm_GlobalTheory_HL_GFrames_Zh_inv_mul


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
theorem _root_.solution : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k), G.Zh⁻¹ * G.Zh = 1 := by
  first | exact @GlobalTheory.HL.GFrames.Zh_inv_mul | exact GlobalTheory.HL.GFrames.Zh_inv_mul | (intros; apply GlobalTheory.HL.GFrames.Zh_inv_mul <;> assumption)
end _root_.GlobalTheory.T
