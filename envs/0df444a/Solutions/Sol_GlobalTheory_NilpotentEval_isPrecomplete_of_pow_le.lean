-- Prove2me | solution 1 for GlobalTheory.NilpotentEval.isPrecomplete_of_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:43:11.091891+00:00
-- url     : https://prove2.me/submissions/4e9a8ebd-271a-461d-a3a4-bdcdfc804e7c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MvPowerSeriesEvalOfPowMem
import Theorems.Thm_GlobalTheory_NilpotentEval_pow_mul_le
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.mvEvalAdic_C
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
open GlobalTheory.NilpotentEval
variable {A : Type*} [CommRing A]
namespace GlobalTheory.NilpotentEval
theorem _root_.solution {K J : Ideal A} {N : ℕ} (h : J ^ N ≤ K) (hKJ : K ≤ J)
    [IsPrecomplete K A] : IsPrecomplete J A := by
  have h' : J ^ (N + 1) ≤ K := (Ideal.pow_le_pow_right N.le_succ).trans h
  refine ⟨fun f hf => ?_⟩
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hf ⊢
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := K) (fun n => f ((N + 1) * n)) fun {m n} hmn => by
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    exact pow_mul_le h' m (hf (Nat.mul_le_mul_left _ hmn))
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hL
  refine ⟨L, fun n => ?_⟩
  have h1 := hf (m := n) (n := (N + 1) * n) (Nat.le_mul_of_pos_left n N.succ_pos)
  have h2 := Ideal.pow_right_mono hKJ n (hL n)
  simpa using add_mem h1 h2
end GlobalTheory.NilpotentEval
