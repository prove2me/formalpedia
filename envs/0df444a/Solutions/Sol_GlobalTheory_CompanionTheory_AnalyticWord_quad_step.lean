-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AnalyticWord.quad_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:17:21.935594+00:00
-- url     : https://prove2.me/submissions/d0fd107f-31d1-48f7-acef-159d4c785229

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SkewAdjointCasimirSpectral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AnalyticWord
variable {V H : Type} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : Type}
namespace GlobalTheory.CompanionTheory.AnalyticWord
theorem _root_.solution {x y A B : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : x ^ 2 ≤ y * (A * y + B * x)) : x ≤ (√A + B) * y := by
  by_contra hlt
  push_neg at hlt
  have hs0 := Real.sqrt_nonneg A
  have hss : √A * √A * (y * y) = A * (y * y) := by rw [Real.mul_self_sqrt hA]
  have hx1 : √A * y ≤ x := by nlinarith [mul_nonneg hB hy]
  have hxpos : 0 < x := lt_of_le_of_lt (mul_nonneg (add_nonneg hs0 hB) hy) hlt
  nlinarith [mul_lt_mul_of_pos_left hlt hxpos, mul_nonneg (sub_nonneg.2 hx1) (mul_nonneg hs0 hy), hss]
end GlobalTheory.CompanionTheory.AnalyticWord
