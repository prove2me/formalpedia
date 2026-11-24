-- Prove2me | solution 1 for GlobalTheory.UnitaryZariskiDense.eval_div_mul_pow_totalDegree_clear_denominators
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:07:20.713568+00:00
-- url     : https://prove2.me/submissions/b10ef58d-034a-49d4-9490-911abaef0b2f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupFamilyZariskiDense
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open Classical MvPolynomial
open scoped Matrix ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.UnitaryZariskiDense
variable {ι : Type} {a : ℕ}
variable [Fintype ι]
namespace GlobalTheory.UnitaryZariskiDense
theorem _root_.solution {σ : Type} (Q : MvPolynomial σ ℂ) (p : σ → ℂ) (D : ℂ) (hD : D ≠ 0) :
    eval (fun v => p v / D) Q * D ^ Q.totalDegree =
      ∑ d ∈ Q.support, coeff d Q * (∏ v ∈ d.support, p v ^ d v) *
        D ^ (Q.totalDegree - d.sum fun _ e => e) := by
  rw [eval_eq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hle := le_totalDegree hd
  have hs : (d.sum fun _ e => e) = ∑ v ∈ d.support, d v := rfl
  have hN : D ^ Q.totalDegree = D ^ (Q.totalDegree - d.sum fun _ e => e) * D ^ (∑ v ∈ d.support, d v) := by
    rw [← hs, ← pow_add, Nat.sub_add_cancel hle]
  simp only [div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
  rw [hN]
  have key : ∀ c P F E : ℂ, E ≠ 0 → c * (P / E) * (F * E) = c * P * F := by
    intro c P F E hE
    calc c * (P / E) * (F * E) = c * P * F * (E / E) := by ring
      _ = c * P * F := by rw [div_self hE, mul_one]
  exact key _ _ _ _ (pow_ne_zero _ hD)
end GlobalTheory.UnitaryZariskiDense
