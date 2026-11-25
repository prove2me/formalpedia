-- Prove2me | solution 1 for GlobalTheory.HL.GlueInt.sig_sig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:39:50.444386+00:00
-- url     : https://prove2.me/submissions/2851bed2-9c62-438c-a27a-98cd2363ef47

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemSpanSingleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfIntegralAllQuadraticCompletions
import Theorems.Thm_P2M_GlobalTheory_HL_GlueInt_nonempty_place__c700acea4894
import Theorems.Thm_GlobalTheory_HL_GlueInt_nontrivial_Ep

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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.GlueInt
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
namespace GlobalTheory.HL.GlueInt
theorem _root_.solution (A : Places F E sig) (y : E) : sig (sig y) = y := by
  obtain ⟨p⟩ := nonempty_place' (F := F)
  haveI := nontrivial_Ep A p
  apply (A.loc p).ιE.injective
  rw [← (A.loc p).cj_ιE, ← (A.loc p).cj_ιE, ← A.L_cj, (A.L p).cj_cj]
end GlobalTheory.HL.GlueInt
