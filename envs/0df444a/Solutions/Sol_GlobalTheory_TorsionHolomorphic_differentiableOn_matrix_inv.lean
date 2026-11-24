-- Prove2me | solution 1 for GlobalTheory.TorsionHolomorphic.differentiableOn_matrix_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:00:09.514057+00:00
-- url     : https://prove2.me/submissions/cba3871a-4f79-4eb2-9031-d4c89af82442

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsDifferentiableOnTorsSq
import Theorems.Thm_GlobalTheory_TorsionHolomorphic_differentiableOn_det

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
    (W : Set E) (hA : ∀ p q, DifferentiableOn ℂ (fun e => A e p q) W)
    (hdet : ∀ e ∈ W, (A e).det ≠ 0) (p q : n) :
    DifferentiableOn ℂ (fun e => (A e)⁻¹ p q) W := by
  have key : ∀ e, (A e)⁻¹ p q = ((A e).det)⁻¹ * (A e).adjugate p q := by
    intro e
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  simp only [key]
  refine (DifferentiableOn.inv (_root_.GlobalTheory.TorsionHolomorphic.differentiableOn_det A W hA) hdet).mul ?_
  simp only [Matrix.adjugate_apply]
  have hentry : ∀ i j, DifferentiableOn ℂ
      (fun e => (A e).updateRow q (Pi.single p 1) i j) W := by
    intro i j
    by_cases hi : i = q
    · subst hi
      simp only [Matrix.updateRow_self]
      exact differentiableOn_const _
    · simp only [Matrix.updateRow_ne hi]
      exact hA i j
  exact _root_.GlobalTheory.TorsionHolomorphic.differentiableOn_det (fun e => (A e).updateRow q (Pi.single p 1))
    W hentry
end _root_.GlobalTheory.TorsionHolomorphic
end GlobalTheory.TorsionHolomorphic
