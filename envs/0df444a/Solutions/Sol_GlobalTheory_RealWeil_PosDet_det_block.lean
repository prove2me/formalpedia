-- Prove2me | solution 1 for GlobalTheory.RealWeil.PosDet.det_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:27:18.363518+00:00
-- url     : https://prove2.me/submissions/6b015de8-41b8-444b-8b82-3495efebc261

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HalfAddSelf
import Theorems.Thm_GlobalTheory_RealWeil_PosDet_det_left
import Theorems.Thm_GlobalTheory_RealWeil_PosDet_det_right
import Theorems.Thm_GlobalTheory_RealWeil_PosDet_det_sign
import Theorems.Thm_GlobalTheory_RealWeil_PosDet_det_diag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.PosDet
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.RealWeil.PosDet
theorem _root_.solution {p : Matrix ι ι ℂ} (pp : p * p = p) {g₁ h₁ g₂ h₂ : Matrix ι ι ℂ} (hg₁ : h₁ * g₁ = 1)
    (hg₂ : h₂ * g₂ = 1) :
    (fromBlocks (p * g₁ * p - (1 - p) * g₁ * (1 - p)) (p * g₂) (-((1 - p) * g₁))
      (p * g₂ * p - (1 - p) * g₂ * (1 - p))).det =
      g₁.det * g₂.det * ((p * h₁ + (1 - p)).det * (p * g₂ + (1 - p)).det * (p * (h₂ * g₁) + (1 - p)).det) := by
  have pp' : ∀ x, p * (p * x) = p * x := fun x => by rw [← mul_assoc, pp]
  have gh : g₂ * h₂ = 1 := mul_eq_one_comm.1 hg₂
  have gh' : ∀ x, g₂ * (h₂ * x) = x := fun x => by rw [← mul_assoc, gh, one_mul]
  have hσ : fromBlocks p (1 - p) (1 - p) p * fromBlocks p (1 - p) (1 - p) p = 1 := by
    rw [fromBlocks_multiply, ← fromBlocks_one]
    congr 1 <;> (simp only [mul_sub, sub_mul, pp, one_mul, mul_one]; abel)
  have e : fromBlocks p (1 - p) (1 - p) p *
      fromBlocks (p * g₁ * p - (1 - p) * g₁ * (1 - p)) (p * g₂) (-((1 - p) * g₁))
      (p * g₂ * p - (1 - p) * g₂ * (1 - p)) * fromBlocks p (1 - p) (1 - p) p =
      fromBlocks ((p - (1 - p)) * g₂ * (h₂ * g₁ * p + (1 - p))) (p * g₂ * p - (1 - p) * g₁ * (1 - p)) 0
        (p * g₂ * p - (1 - p) * g₁ * (1 - p)) := by
    rw [fromBlocks_multiply, fromBlocks_multiply]
    congr 1 <;> (simp only [mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, mul_assoc, pp, pp', gh', one_mul, mul_one]; abel)
  have d := congrArg det e
  have dσ := congrArg det hσ
  rw [det_mul, det_one] at dσ
  rw [det_mul, det_mul, det_fromBlocks_zero₂₁, det_diag pp g₂ hg₁, det_mul, det_mul, det_right pp,
    ← det_left pp, mul_right_comm, dσ, one_mul] at d
  rw [d]
  linear_combination (g₁.det * g₂.det * ((p * h₁ + (1 - p)).det * (p * g₂ + (1 - p)).det *
    (p * (h₂ * g₁) + (1 - p)).det)) * det_sign pp
end GlobalTheory.RealWeil.PosDet
