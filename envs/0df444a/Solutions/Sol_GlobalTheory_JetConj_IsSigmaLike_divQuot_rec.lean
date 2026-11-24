-- Prove2me | solution 1 for GlobalTheory.JetConj.IsSigmaLike.divQuot_rec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:59:26.590453+00:00
-- url     : https://prove2.me/submissions/4f8ac753-e0f1-4244-9242-ccc775ffad09

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JetRelOfWeierstrassSystem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SecondDerivSigmaProductAtZero
import Theorems.Thm_GlobalTheory_JetConj_wr_congr
import Theorems.Thm_GlobalTheory_JetConj_wr_mul
import Theorems.Thm_GlobalTheory_JetConj_wr_pow
import Theorems.Thm_GlobalTheory_JetConj_wr_affine
import Theorems.Thm_GlobalTheory_JetConj_IsSigmaLike_add_wr
import Theorems.Thm_GlobalTheory_JetConj_IsSigmaLike_analyticAt_divQuot
import Theorems.Thm_GlobalTheory_JetConj_eventually_add_notMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology PeriodPair
open GlobalTheory GlobalTheory.JetConj
variable {L : PeriodPair} {σ : ℂ → ℂ}
namespace GlobalTheory.JetConj
namespace IsSigmaLike
theorem _root_.solution (H : IsSigmaLike L σ) {u z : ℂ} (hz : z + u ∉ L.lattice) (n : ℕ) :
    divQuot σ u (n + 2) z * (((n + 1 : ℕ) : ℂ) ^ 2 * divQuot σ u n z) = wr (divQuot σ u (n + 1)) z := by
  have hσ := H.diff
  have h0 : σ (z + u) ≠ 0 := mt (H.zero_iff _).1 hz
  have b : Differentiable ℂ fun z => σ (z + u) := by fun_prop
  have e : (fun w => σ ((n + 1 : ℕ) * w + (n + 1 : ℕ) * u)) =ᶠ[𝓝 z]
      fun w => divQuot σ u (n + 1) w * σ (w + u) ^ ((n + 1) ^ 2) := by
    filter_upwards [eventually_add_notMem L hz] with w hw
    rw [divQuot, div_mul_cancel₀ _ (pow_ne_zero _ (mt (H.zero_iff _).1 hw))]
  have e1 := wr_congr e
  rw [wr_affine hσ, wr_mul (H.analyticAt_divQuot hz _) ((b.analyticAt z).fun_pow _)] at e1
  have e2 := wr_pow (b.analyticAt z) ((n + 1) ^ 2)
  have e3 := wr_affine hσ 1 u z
  simp only [one_mul, one_pow] at e3
  rw [e3] at e2
  have e4 := H.add_wr ((n + 1 : ℕ) * z + (n + 1 : ℕ) * u) hz
  have e5 := e.eq_of_nhds
  rw [show ((n + 1 : ℕ) : ℂ) * z + (n + 1 : ℕ) * u + (z + u) = (n + 2 : ℕ) * z + (n + 2 : ℕ) * u by
    push_cast; ring, show ((n + 1 : ℕ) : ℂ) * z + (n + 1 : ℕ) * u - (z + u) = n * z + n * u by
    push_cast; ring, e5] at e4
  have e6 : σ (z + u) ^ ((n + 2) ^ 2) * σ (z + u) ^ (n ^ 2) =
      (σ (z + u) ^ ((n + 1) ^ 2)) ^ 2 * σ (z + u) ^ 2 := by ring
  have h7 : σ (z + u) ^ ((n + 1) ^ 2) ≠ 0 := pow_ne_zero _ h0
  rw [divQuot, divQuot, div_mul_eq_mul_div, ← mul_div_assoc, ← mul_div_assoc, div_div, mul_comm (σ (z + u) ^ (n ^ 2)), e6,
    div_eq_iff (mul_ne_zero (pow_ne_zero _ h7) (pow_ne_zero _ h0))]
  push_cast at *
  linear_combination ((n : ℂ) + 1) ^ 2 * e4 + σ (z + u) ^ 2 * e1 + divQuot σ u (n + 1) z ^ 2 * e2
end IsSigmaLike
end GlobalTheory.JetConj
