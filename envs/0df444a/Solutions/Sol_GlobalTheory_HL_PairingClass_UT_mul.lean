-- Prove2me | solution 1 for GlobalTheory.HL.PairingClass.UT.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:58:19.77224+00:00
-- url     : https://prove2.me/submissions/941bb998-48b8-4164-b7b7-b31859a24fa0

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NotField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermOverRelationUniqueness
import Theorems.Thm_GlobalTheory_HL_PairingClass_diag_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.PairingClass
variable {E : Type} [CommRing E] {n : ℕ}
namespace GlobalTheory.HL.PairingClass
namespace UT
theorem _root_.solution {A B : Matrix (Fin n) (Fin n) E} (hA : UT A) (hB : UT B) : UT (A * B) := by
  refine ⟨fun i j h => ?_, fun i => by rw [diag_mul hA.1 hB.1, hA.2, hB.2, one_mul]⟩
  have h1 : A.BlockTriangular id := fun i j h => hA.1 i j h
  have h2 : B.BlockTriangular id := fun i j h => hB.1 i j h
  exact (h1.mul h2) h
end UT
end GlobalTheory.HL.PairingClass
