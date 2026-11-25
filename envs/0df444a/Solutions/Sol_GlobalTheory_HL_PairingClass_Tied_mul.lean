-- Prove2me | solution 1 for GlobalTheory.HL.PairingClass.Tied.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:01:53.201954+00:00
-- url     : https://prove2.me/submissions/4388d60e-9731-4b1f-a716-fbd9cf287710

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
import Theorems.Thm_GlobalTheory_HL_PairingClass_UT_mul
import Theorems.Thm_GlobalTheory_HL_PairingClass_IntM_mul

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
namespace Tied
theorem _root_.solution {O : Subring E} {θ : E} {A A' B B' : Matrix (Fin n) (Fin n) E}
    (hA : Tied O θ A A') (hB : Tied O θ B B') : Tied O θ (A * B) (A' * B') := by
  obtain ⟨a1, a2, a3, a4, C, hC, e1⟩ := hA
  obtain ⟨b1, b2, b3, b4, D, hD, e2⟩ := hB
  refine ⟨a1.mul b1, a2.mul b2, a3.mul b3, a4.mul b4, A * D + C * B', fun i j => ?_, ?_⟩
  · exact O.add_mem (a3.mul hD i j) (hC.mul b4 i j)
  · have h : A * B' = A * B + θ • (A * D) := by rw [e2, mul_add, Matrix.mul_smul]
    rw [e1, add_mul, smul_add, Matrix.smul_mul, ← add_assoc, ← h]
end Tied
end GlobalTheory.HL.PairingClass
