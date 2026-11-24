-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertGenFun.hasSum_counts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:05:51.16559+00:00
-- url     : https://prove2.me/submissions/9eaf0a55-27c1-4f23-bf4b-5eadf75e01f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_GeneratingFunctionIdentity
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_val_mid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] GlobalTheory.InertZeta.blk_last
attribute [local simp] GlobalTheory.InertZeta.blk_mid
attribute [local simp] GlobalTheory.InertZeta.blk_zero
attribute [local simp] GlobalTheory.InertZeta.val_mid



set_option autoImplicit false
open GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertGenFun
namespace GlobalTheory.CompanionTheory.InertGenFun
theorem _root_.solution (q N c : ℕ) (X : ℂ) (h : ‖(q : ℂ) ^ (N + 1) * X‖ < 1) :
    HasSum (fun j : ℕ => ((c * q ^ (2 * N * (j / 2) + j) : ℕ) : ℂ) * X ^ j)
      (c * (1 + q * X) / (1 - ((q : ℂ) ^ (N + 1) * X) ^ 2)) := by
  set y : ℂ := (q : ℂ) ^ (N + 1) * X with hy
  set F : ℕ → ℂ := fun j => ((c * q ^ (2 * N * (j / 2) + j) : ℕ) : ℂ) * X ^ j with hF
  have hy2 : ‖y ^ 2‖ < 1 := by
    rw [norm_pow]
    nlinarith [norm_nonneg y]
  have hg := hasSum_geometric_of_norm_lt_one hy2
  have hev : HasSum (fun m : ℕ => F (2 * m)) (c * (1 - y ^ 2)⁻¹) := by
    have hfun : (fun m : ℕ => F (2 * m)) = fun m => (c : ℂ) * (y ^ 2) ^ m := by
      funext m
      simp only [hF]
      rw [Nat.mul_div_cancel_left m (by norm_num : 0 < 2), hy]
      push_cast
      ring
    rw [hfun]
    exact hg.mul_left _
  have hodd : HasSum (fun m : ℕ => F (2 * m + 1)) (c * q * X * (1 - y ^ 2)⁻¹) := by
    have hfun : (fun m : ℕ => F (2 * m + 1)) = fun m => (c * q * X : ℂ) * (y ^ 2) ^ m := by
      funext m
      simp only [hF]
      rw [show (2 * m + 1) / 2 = m by omega, hy]
      push_cast
      ring
    rw [hfun]
    exact hg.mul_left _
  have hne : (1 : ℂ) - y ^ 2 ≠ 0 := by
    intro h0
    have : ‖y ^ 2‖ = 1 := by
      rw [show y ^ 2 = 1 by linear_combination -h0]
      simp
    linarith
  have hval : (c : ℂ) * (1 + q * X) / (1 - y ^ 2) = c * (1 - y ^ 2)⁻¹ + c * q * X * (1 - y ^ 2)⁻¹ := by
    field_simp
  rw [hval]
  exact HasSum.even_add_odd hev hodd
end GlobalTheory.CompanionTheory.InertGenFun
