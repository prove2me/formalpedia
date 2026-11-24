-- Prove2me | solution 1 for GlobalTheory.BorelUMod.Cayley.cay_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:42:18.057833+00:00
-- url     : https://prove2.me/submissions/e15e17ee-caf7-4e66-806c-3fc1c0af3c4f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowApplyEqZeroOfStrictUpper
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexEqOfSurj
import Theorems.Thm_GlobalTheory_BorelUMod_Cayley_exists_inv
import Theorems.Thm_GlobalTheory_BorelUMod_adjJ_add
import Theorems.Thm_GlobalTheory_BorelUMod_adjJ_mul
import Theorems.Thm_GlobalTheory_BorelUMod_adjJ_smul
import Theorems.Thm_GlobalTheory_BorelUMod_mem_skewJ
import Theorems.Thm_GlobalTheory_BorelUMod_smul_mem_upLat
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero



set_option autoImplicit false
open GlobalTheory.LGrp GlobalTheory.BorelUMod Formalism.UG
noncomputable section
open GlobalTheory GlobalTheory.BorelUMod GlobalTheory.BorelUMod.Cayley
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
namespace GlobalTheory.BorelUMod.Cayley
theorem _root_.solution {c : Fin n → Fin n → ℤ} (hc : IsWeight c) {σ : L →+* L} (hσσ : ∀ x, σ (σ x) = x) {t : L}
    (ht : Valued.v t ≤ 1) (hσ : t + σ t = 1) {X : Matrix (Fin n) (Fin n) L} (hX : X ∈ upLat L c)
    (hs : X ∈ skewJ σ n) : ∃ u, u - 1 ∈ upLat L c ∧ adjJ σ u * u = 1 ∧ cay t u = X := by
  obtain ⟨z, hz, e1, e2⟩ := exists_inv hc (neg_mem (smul_mem_upLat ht hX))
  rw [mem_skewJ] at hs
  have hst : σ t = 1 - t := by linear_combination hσ
  have e3 := congrArg (adjJ σ) e1
  rw [← sub_eq_add_neg] at e1 e2 e3
  rw [adjJ_mul, adjJ_one, adjJ_sub, adjJ_smul, adjJ_one, hs, smul_neg, sub_neg_eq_add] at e3
  set T := 1 + z with hT
  have h1 : (1 + σ t • X) * T - 1 = X * T := by
    have : (1 + σ t • X) = X + (1 - t • X) := by rw [hst]; module
    rw [this, add_mul, e1, add_sub_cancel_right]
  refine ⟨(1 + σ t • X) * T, ?_, ?_, ?_⟩
  · rw [h1, hT, mul_add, mul_one]
    exact add_mem hX (mul_mem_upLat hc.2 hX hz)
  · rw [adjJ_mul, adjJ_add σ 1 (σ t • X), adjJ_smul, adjJ_one, hs, hσσ, smul_neg, ← sub_eq_add_neg]
    have : (1 - t • X) * (1 + σ t • X) = (1 + σ t • X) * (1 - t • X) := by
      simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
      module
    rw [mul_assoc, ← mul_assoc (1 - t • X), this, mul_assoc, e1, mul_one, e3]
  · have h2 : 1 + t • (X * T) = T := by
      have := e1
      rw [sub_mul, one_mul, smul_mul_assoc] at this
      rw [← this]; abel
    have h3 : (1 - t • X) * X = X * (1 - t • X) := by
      simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    rw [cay, h1, h2, Matrix.inv_eq_left_inv e1, ← mul_assoc, h3, mul_assoc, e1, mul_one]
end GlobalTheory.BorelUMod.Cayley
