-- Prove2me | solution 1 for GlobalTheory.GramCount.quotInv_quotInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:49:41.530571+00:00
-- url     : https://prove2.me/submissions/621270b8-b26c-442c-acc3-4e634c8acd83

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimitiveTuplesWithGramMatrixHenselCountStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NcardPrimitiveTuplesGramModNilpotentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardHermitianMatricesDvdSqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NcardPrimitiveTuplesWithGramMatrixResidueRingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardPrimitiveTuplesHermitianGramModUniformizer
import Theorems.Thm_GlobalTheory_GramCount_quotInv_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.GramCount
variable {O : Type} [CommRing O]
namespace GlobalTheory.GramCount
theorem _root_.solution (c : O →+* O) (hc : ∀ u, c (c u) = u) (p : O) (hp : c p = p) (u) :
    quotInv c p hp (quotInv c p hp u) = u := by
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective u
  rw [quotInv_mk, quotInv_mk, hc]
end GlobalTheory.GramCount
