-- Prove2me | solution 1 for GlobalTheory.HL.TypeRep.spanTo_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:56:11.068819+00:00
-- url     : https://prove2.me/submissions/0d2323eb-5fbf-41a7-9b92-553a880f9d94

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermLevelZeroAndBoundedRepresentativesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PairingSecondTypeTestOnRepresentatives

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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.TypeRep
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.TypeRep
theorem _root_.solution (g : Fin (r + 1) → S.V) : S.spanTo g r ≤ S.spanTo g (r + 1) := by
  unfold Frames.spanTo
  exact Submodule.span_mono (Set.image_mono fun i (hi : (i : ℕ) < r) => Nat.lt_succ_of_lt hi)
end GlobalTheory.HL.TypeRep
