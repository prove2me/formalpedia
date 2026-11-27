-- Prove2me | solution 1 for GlobalTheory.rowAdd_invariant_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:40:59.319251+00:00
-- url     : https://prove2.me/submissions/95e14345-87b0-48ea-adba-80fa9f284f73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_RowAddGenericRowAddTerm
import Theorems.Thm_GlobalTheory_eval_rowAddGeneric
import Theorems.Thm_GlobalTheory_eval_zero_rowAddGeneric
import Theorems.Thm_GlobalTheory_derivative_rowAddGeneric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory
set_option linter.unusedVariables false
namespace GlobalTheory
theorem _root_.solution {K σ ι : Type*} [Field K] [CharZero K] [DecidableEq σ] [Fintype ι]
    (u w : ι → σ) (hw : Function.Injective w)
    (huw : ∀ k l, u k ≠ w l) (P : MvPolynomial σ K) :
    List.TFAE [∀ t : ℤ, bind₁ (fun s => X s + ∑ k, if s = w k then C (t : K) * X (u k) else 0) P = P,
      ∀ t : K, bind₁ (fun s => X s + ∑ k, if s = w k then C t * X (u k) else 0) P = P,
      ∑ k, X (u k) * pderiv (w k) P = 0] := by
  tfae_have 2 → 1 := fun h t => h t
  tfae_have 1 → 3 := by
    intro h
    have hc : rowAddGeneric u w P = Polynomial.C P := by
      apply Polynomial.eq_of_infinite_eval_eq
      have hinj : Function.Injective fun t : ℤ => (C (t : K) : MvPolynomial σ K) :=
        fun a b hab => Int.cast_injective (C_injective σ K hab)
      refine Set.infinite_of_injective_forall_mem hinj fun t => ?_
      simp only [Set.mem_ofPred_eq, Polynomial.eval_C]
      rw [eval_rowAddGeneric, h t]
    have hd := derivative_rowAddGeneric u w huw P
    rw [hc, Polynomial.derivative_C] at hd
    rw [← eval_zero_rowAddGeneric u w (∑ k, X (u k) * pderiv (w k) P), ← hd, Polynomial.eval_zero]
  tfae_have 3 → 2 := by
    intro h t
    have hd := derivative_rowAddGeneric u w huw P
    rw [h, map_zero] at hd
    have hc := Polynomial.eq_C_of_derivative_eq_zero hd
    rw [← eval_rowAddGeneric]
    conv_rhs => rw [← eval_zero_rowAddGeneric u w P]
    rw [hc, Polynomial.eval_C, Polynomial.eval_C]
  tfae_finish
end GlobalTheory
