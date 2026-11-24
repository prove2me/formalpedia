-- Prove2me | solution 1 for GlobalTheory.InertZeta.HasLen.mul_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:54:04.832233+00:00
-- url     : https://prove2.me/submissions/d681db33-235f-4984-bee6-9a5adf7fe378

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Theorems.Thm_GlobalTheory_InertZeta_IsInt_mul
import Theorems.Thm_GlobalTheory_InertZeta_v_det_eq_one
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
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
namespace HasLen
theorem _root_.solution {g a a' b b' : Matrix (Fin n) (Fin n) L} {k : ℕ} (h : HasLen g k) (ha : IsInt a)
    (ha' : IsInt a') (hb : IsInt b) (hb' : IsInt b') (ea : a' * a = 1) (eb : b * b' = 1) : HasLen (a * g * b) k := by
  obtain ⟨U, V, C, ⟨h1, h2, h3, h4, h5⟩, e⟩ := h
  refine ⟨U * b, V * a', b' * C, ⟨h1.mul hb, h2.mul ha', hb'.mul h3, ?_, ?_⟩, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc b, eb, Matrix.one_mul, Matrix.mul_assoc]
    exact ha.mul h4
  · calc _ = (U + V * (a' * a) * g) * (b * b') * C := by simp only [Matrix.add_mul, Matrix.mul_assoc]
      _ = 1 := by rw [ea, eb, Matrix.mul_one, Matrix.mul_one, h5]
  · rw [Matrix.det_mul, map_mul, v_det_eq_one hb' hb (mul_eq_one_comm.1 eb), one_mul, e]
end HasLen
end GlobalTheory.InertZeta
