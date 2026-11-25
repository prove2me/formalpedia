-- Prove2me | solution 1 for GlobalTheory.HL.PrimTerm.Mof_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:22:01.319642+00:00
-- url     : https://prove2.me/submissions/f2e38441-0476-4ef3-aef4-8ffc52f56590

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnesses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SelfDualLatticeUnipotentTranslateStandard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemSpanOfMemMof
import Theorems.Thm_GlobalTheory_HL_PrimTerm_Mof_le_swap

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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.PrimTerm
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.PrimTerm
theorem _root_.solution (h0 : S.th ≠ 0) (hO : algebraMap F E S.th ∈ L.O) (g g' : Fin (r + 1) → S.V) :
    S.Mof g' g = S.Mof g g' :=
  le_antisymm (Mof_le_swap S h0 hO g g') (Mof_le_swap S h0 hO g' g)
end GlobalTheory.HL.PrimTerm
