-- Prove2me | solution 1 for GlobalTheory.InertZeta.IsFrac.v_det_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:45:52.186356+00:00
-- url     : https://prove2.me/submissions/4c4ffc99-b020-41c2-8485-bc9e2664143d

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Theorems.Thm_GlobalTheory_InertZeta_IsInt_mul
import Theorems.Thm_GlobalTheory_InertZeta_IsInt_add
import Theorems.Thm_GlobalTheory_InertZeta_IsInt_v_det_le
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_UnitarySwap_SelfDual_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix MeasureTheory GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
namespace GlobalTheory.InertZeta
namespace IsFrac
theorem _root_.solution {g U V C U' V' C' : Matrix (Fin n) (Fin n) L} (h : IsFrac g U V C) (h' : IsFrac g U' V' C') :
    Valued.v C'.det ≤ Valued.v C.det := by
  have e : C' = C * (U * C' + V * (g * C')) := by
    rw [← Matrix.mul_assoc V, ← Matrix.add_mul, ← Matrix.mul_assoc, mul_eq_one_comm.1 h.2.2.2.2, Matrix.one_mul]
  rw [e, Matrix.det_mul, map_mul]
  exact mul_le_of_le_one_right' ((h.1.mul h'.2.2.1).add (h.2.1.mul h'.2.2.2.1)).v_det_le
end IsFrac
end GlobalTheory.InertZeta
