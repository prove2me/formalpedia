-- Prove2me | solution 1 for GlobalTheory.TorsionHolomorphic.differentiableOn_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:48:17.875221+00:00
-- url     : https://prove2.me/submissions/803df14f-3fdb-44e0-84b4-63b99a5cd5b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsDifferentiableOnTorsSq
import Theorems.Thm_GlobalTheory_TorsionHolomorphic_differentiableOn_finset_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.TorsionHolomorphic
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.TorsionHolomorphic
namespace _root_.GlobalTheory.TorsionHolomorphic
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] (A : E → Matrix n n ℂ)
    (W : Set E) (hA : ∀ p q, DifferentiableOn ℂ (fun e => A e p q) W) :
    DifferentiableOn ℂ (fun e => (A e).det) W := by
  have hdet : (fun e => (A e).det) =
      fun e => ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A e (σ i) i := by
    funext e
    exact Matrix.det_apply' _
  rw [hdet]
  refine DifferentiableOn.fun_sum (fun σ _ => ?_)
  exact (differentiableOn_const _).mul
    (_root_.GlobalTheory.TorsionHolomorphic.differentiableOn_finset_prod Finset.univ (fun i e => A e (σ i) i) W
      (fun i => hA _ _))
end _root_.GlobalTheory.TorsionHolomorphic
end GlobalTheory.TorsionHolomorphic
