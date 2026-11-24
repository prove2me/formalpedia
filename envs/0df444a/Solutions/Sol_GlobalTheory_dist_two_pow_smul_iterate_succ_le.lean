-- Prove2me | solution 1 for GlobalTheory.dist_two_pow_smul_iterate_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:40:33.700876+00:00
-- url     : https://prove2.me/submissions/c19ba869-f219-4827-bbfd-06e72837933a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Theorems.Thm_GlobalTheory_norm_iterate_le_of_contraction
import Theorems.Thm_GlobalTheory_iterate_mem_ball_of_contraction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter Asymptotics
open scoped Topology
open GlobalTheory
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {ε : V → V} {r C : ℝ}
namespace GlobalTheory
theorem _root_.solution (hc : ∀ x ∈ ball (0 : V) r, ‖ε x‖ ≤ 5 / 8 * ‖x‖)
    (hC0 : 0 ≤ C) (hC : ∀ x ∈ ball (0 : V) r, ‖ε x - (2 : ℂ)⁻¹ • x‖ ≤ C * ‖x‖ ^ 2)
    {x : V} (hx : x ∈ ball (0 : V) r) (j : ℕ) :
    dist ((2 : ℂ) ^ j • ε^[j] x) ((2 : ℂ) ^ (j + 1) • ε^[j + 1] x)
      ≤ 2 * C * ‖x‖ ^ 2 * (25 / 32) ^ j := by
  have h1 := hC _ (iterate_mem_ball_of_contraction hc hx j)
  have h2 := norm_iterate_le_of_contraction hc hx j
  have e : (2 : ℂ) ^ (j + 1) • ε^[j + 1] x - (2 : ℂ) ^ j • ε^[j] x
      = (2 : ℂ) ^ (j + 1) • (ε (ε^[j] x) - (2 : ℂ)⁻¹ • ε^[j] x) := by
    rw [Function.iterate_succ_apply', smul_sub, smul_smul, pow_succ (2 : ℂ) j,
      mul_inv_cancel_right₀ two_ne_zero]
  rw [dist_comm, dist_eq_norm, e, norm_smul, norm_pow, Complex.norm_two]
  calc (2 : ℝ) ^ (j + 1) * ‖ε (ε^[j] x) - (2 : ℂ)⁻¹ • ε^[j] x‖
      ≤ 2 ^ (j + 1) * (C * ((5 / 8) ^ j * ‖x‖) ^ 2) := by
        gcongr
        exact h1.trans (by gcongr)
    _ = 2 * C * ‖x‖ ^ 2 * (2 * (5 / 8) ^ 2) ^ j := by
        rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm j 2]
        ring
    _ = _ := by norm_num
end GlobalTheory
