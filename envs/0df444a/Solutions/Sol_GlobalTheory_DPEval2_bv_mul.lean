-- Prove2me | solution 1 for GlobalTheory.DPEval2.bv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:34:26.265827+00:00
-- url     : https://prove2.me/submissions/c303da8c-9fd6-43de-ace3-7529769e4079

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDividedPowerEvalTwoVarsRingHom
import Theorems.Thm_GlobalTheory_DPEval2_ex_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DPEval2
namespace GlobalTheory.DPEval2
theorem _root_.solution (p q : ℕ × ℕ) :
    bv p * bv q = ((p.1 + q.1).choose p.1 * (p.2 + q.2).choose p.2 : ℕ) • bv (p + q) := by
  rw [bv_eq, bv_eq, bv_eq, smul_mul_smul, monomial_mul, ← ex_add, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul,
    mul_one]
  congr 1
  simp only [Prod.fst_add, Prod.snd_add, Nat.cast_mul, Nat.cast_add_choose]
  field_simp
end GlobalTheory.DPEval2
