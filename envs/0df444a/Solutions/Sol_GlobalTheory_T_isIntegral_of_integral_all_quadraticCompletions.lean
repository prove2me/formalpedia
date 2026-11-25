-- Prove2me | solution 1 for GlobalTheory.T.isIntegral_of_integral_all_quadraticCompletions
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:25:48.780413+00:00
-- url     : https://prove2.me/submissions/3fa5d215-f5d0-473e-8176-aa98d36123ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfIntegralAllQuadraticCompletions
import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemSpanSingleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfIntegralAllQuadraticCompletionsStatement
import Theorems.Thm_GlobalTheory_HL_isIntegral_of_forall_mem_O


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
theorem _root_.solution : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (y : E), (∀ p, (A.loc p).ιE y ∈ (A.L p).O) → IsIntegral ℤ y := by
  first | exact @GlobalTheory.HL.isIntegral_of_forall_mem_O | exact GlobalTheory.HL.isIntegral_of_forall_mem_O | (intros; apply GlobalTheory.HL.isIntegral_of_forall_mem_O <;> assumption)
end _root_.GlobalTheory.T
