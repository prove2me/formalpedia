-- Prove2me | solution 1 for GlobalTheory.TorsionHolomorphic.differentiableOn_matrix_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:32:24.457071+00:00
-- url     : https://prove2.me/submissions/1bb4e1e3-29c5-46f8-a2ea-954fbd00ccf7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsDifferentiableOnTorsSq

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
theorem _root_.solution {n : Type} [Fintype n] (A B : E → Matrix n n ℂ)
    (W : Set E) (hA : ∀ p q, DifferentiableOn ℂ (fun e => A e p q) W)
    (hB : ∀ p q, DifferentiableOn ℂ (fun e => B e p q) W) (p q : n) :
    DifferentiableOn ℂ (fun e => (A e * B e) p q) W := by
  simp only [Matrix.mul_apply]
  exact DifferentiableOn.fun_sum (fun r _ => (hA p r).mul (hB r q))
end _root_.GlobalTheory.TorsionHolomorphic
end GlobalTheory.TorsionHolomorphic
