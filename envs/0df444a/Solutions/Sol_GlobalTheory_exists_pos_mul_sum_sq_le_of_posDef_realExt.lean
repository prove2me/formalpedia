-- Prove2me | solution 1 for GlobalTheory.exists_pos_mul_sum_sq_le_of_posDef_realExt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:56:42.216924+00:00
-- url     : https://prove2.me/submissions/85c772bf-0010-4fae-a6b4-d815ad6410d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBimultiplicativeOfSecondQuotConst
import Theorems.Thm_GlobalTheory_exists_pos_mul_norm_sq_le_of_posDef
import Theorems.Thm_GlobalTheory_realExtBilin_tmul
import Theorems.Thm_GlobalTheory_realExt_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.realExtBilin_tmul
attribute [local simp] GlobalTheory.realExt_tmul

set_option autoImplicit false
open Filter Module TensorProduct
open GlobalTheory
variable {X : Type*} [AddCommGroup X]
namespace GlobalTheory
theorem _root_.solution {ι : Type*} [Fintype ι] (b : Basis ι ℤ X)
    {Q : QuadraticMap ℤ X ℝ} (hQ : (realExt Q).PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, c * ∑ i, (b.repr x i : ℝ) ^ 2 ≤ Q x := by
  let e : EuclideanSpace ℝ ι ≃ₗ[ℝ] ℝ ⊗[ℤ] X :=
    (WithLp.linearEquiv 2 ℝ (ι → ℝ)).trans (b.baseChange ℝ).equivFun.symm
  obtain ⟨c, hc, h⟩ := exists_pos_mul_norm_sq_le_of_posDef (Q := (realExt Q).comp e.toLinearMap)
    (fun v hv => hQ _ (by simpa using hv))
  refine ⟨c, hc, fun x => ?_⟩
  have h₁ := h (e.symm (1 ⊗ₜ x))
  rw [EuclideanSpace.real_norm_sq_eq, QuadraticMap.comp_apply, LinearEquiv.coe_coe,
    e.apply_symm_apply] at h₁
  simpa [e] using h₁
end GlobalTheory
