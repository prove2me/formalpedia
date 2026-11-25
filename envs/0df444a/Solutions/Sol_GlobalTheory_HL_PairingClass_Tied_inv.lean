-- Prove2me | solution 1 for GlobalTheory.HL.PairingClass.Tied.inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:14:28.871888+00:00
-- url     : https://prove2.me/submissions/691e5dcf-3bce-4fd4-ae72-8366451a6796

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
import Theorems.Thm_GlobalTheory_HL_PairingClass_UT_inv
import Theorems.Thm_GlobalTheory_HL_PairingClass_Tied_mul

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
theorem _root_.solution {O : Subring E} {θ : E} {A A' : Matrix (Fin n) (Fin n) E} (hA : Tied O θ A A') :
    ∃ B B', Tied O θ B B' ∧ A * B = 1 ∧ B * A = 1 ∧ A' * B' = 1 ∧ B' * A' = 1 := by
  obtain ⟨a1, a2, a3, a4, C, hC, e1⟩ := hA
  obtain ⟨B, b1, b2, b3, b4⟩ := a1.inv
  obtain ⟨B', c1, c2, c3, c4⟩ := a2.inv
  refine ⟨B, B', ⟨b1, c1, b4 O a3, c4 O a4, -(B' * C * B), fun i j => ?_, ?_⟩, b2, b3, c2, c3⟩
  · exact O.neg_mem (((c4 O a4).mul hC).mul (b4 O a3) i j)
  · have h : θ • C = A' - A := by rw [e1]; abel
    rw [smul_neg, ← Matrix.smul_mul, ← Matrix.mul_smul, h, mul_sub, sub_mul, c3, one_mul,
      mul_assoc, b2, mul_one]
    abel
end Tied
end GlobalTheory.HL.PairingClass
