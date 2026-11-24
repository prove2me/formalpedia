-- Prove2me | solution 1 for GlobalTheory.InertZeta.len_mul_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:04:38.943192+00:00
-- url     : https://prove2.me/submissions/a486bd65-efa7-419f-a8d0-39121717d6a0

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Theorems.Thm_GlobalTheory_InertZeta_HasLen_mul_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf



set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix MeasureTheory GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
namespace GlobalTheory.InertZeta
theorem _root_.solution {g a a' b b' : Matrix (Fin n) (Fin n) L} (ha : IsInt a)
    (ha' : IsInt a') (hb : IsInt b) (hb' : IsInt b') (ea : a' * a = 1) (eb : b * b' = 1) : len (a * g * b) = len g := by
  unfold len
  congr 1
  ext k
  refine ⟨fun h => ?_, fun h => HasLen.mul_mul h ha ha' hb hb' ea eb⟩
  have := HasLen.mul_mul h ha' ha hb' hb (mul_eq_one_comm.1 ea) (mul_eq_one_comm.1 eb)
  rwa [show a' * (a * g * b) * b' = (a' * a) * g * (b * b') by simp only [Matrix.mul_assoc], ea, eb, Matrix.one_mul,
    Matrix.mul_one] at this
end GlobalTheory.InertZeta
