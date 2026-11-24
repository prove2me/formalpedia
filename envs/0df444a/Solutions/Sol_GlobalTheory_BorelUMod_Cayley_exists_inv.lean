-- Prove2me | solution 1 for GlobalTheory.BorelUMod.Cayley.exists_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:24:49.262837+00:00
-- url     : https://prove2.me/submissions/e113a8e1-2c9d-4a18-a4c8-ddca1fe62e08

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowApplyEqZeroOfStrictUpper
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexEqOfSurj
import Theorems.Thm_GlobalTheory_BorelUMod_Cayley_pow_apply_eq_zero
import Theorems.Thm_GlobalTheory_BorelUMod_Cayley_pow_succ_mem
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
theorem _root_.solution {c : Fin n → Fin n → ℤ} (hc : IsWeight c) {y : Matrix (Fin n) (Fin n) L}
    (hy : y ∈ upLat L c) : ∃ z ∈ upLat L c, (1 + y) * (1 + z) = 1 ∧ (1 + z) * (1 + y) = 1 := by
  have hy' : -y ∈ upLat L c := neg_mem hy
  have h0 : (-y) ^ (n + 1) = 0 := by
    ext i j
    exact pow_apply_eq_zero hy'.1 _ i j (by have := j.2; omega)
  have h1 : (1 + y) * (1 + ∑ k ∈ Finset.range n, (-y) ^ (k + 1)) = 1 := by
    have := mul_neg_geom_sum (-y) (n + 1)
    rw [h0, sub_zero, sub_neg_eq_add, Finset.sum_range_succ', pow_zero, add_comm _ (1 : Matrix (Fin n) (Fin n) L)] at this
    simpa [add_comm] using this
  exact ⟨_, sum_mem fun k _ => pow_succ_mem hc hy' k, h1, mul_eq_one_comm.1 h1⟩
end GlobalTheory.BorelUMod.Cayley
