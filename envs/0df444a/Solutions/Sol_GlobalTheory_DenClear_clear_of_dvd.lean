-- Prove2me | solution 1 for GlobalTheory.DenClear.clear_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:02:33.970802+00:00
-- url     : https://prove2.me/submissions/6988fc56-b900-4c71-b298-890893457158

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
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntSmulMemLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsCommonDenominatorForHermitianLatticeData
import Theorems.Thm_GlobalTheory_DenClear_coeO_mul
import Theorems.Thm_GlobalTheory_DenClear_coeO_int

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
open GlobalTheory GlobalTheory.DenClear
namespace GlobalTheory.DenClear
theorem _root_.solution {E : Type} [Field E] [NumberField E] {m D : ℤ} (h : m ∣ D) {e : E}
    (he : ∃ o : 𝓞 E, (m : E) * e = o) : ∃ o : 𝓞 E, (D : E) * e = o := by
  obtain ⟨k, rfl⟩ := h
  obtain ⟨o, ho⟩ := he
  refine ⟨(k : 𝓞 E) * o, ?_⟩
  rw [coeO_mul, coeO_int, ← ho]
  push_cast
  ring
end GlobalTheory.DenClear
