-- Prove2me | solution 1 for GlobalTheory.PrincipalLogDeriv.norm_logDeriv_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:54:10.542165+00:00
-- url     : https://prove2.me/submissions/83cd9997-d466-4394-a692-67f468f8b0b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivRiemannZetaLocalZeroSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NegReLogDerivPrincipalLFunctionLe
import Theorems.Thm_GlobalTheory_PrincipalLogDeriv_one_sub_ne_zero
import Theorems.Thm_GlobalTheory_PrincipalLogDeriv_hasDerivAt_factor
import Theorems.Thm_GlobalTheory_PrincipalLogDeriv_norm_logDeriv_factor_le
import Theorems.Thm_GlobalTheory_PrincipalLogDeriv_sum_log_primeFactors_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.PrincipalLogDeriv
namespace GlobalTheory.PrincipalLogDeriv
theorem _root_.solution (q : ℕ) [NeZero q] {s : ℂ} (hs : 1 < s.re) :
    ‖deriv (LFunction (1 : DirichletCharacter ℂ q)) s / LFunction (1 : DirichletCharacter ℂ q) s
      - deriv riemannZeta s / riemannZeta s‖ ≤ Real.log q := by
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs
    exact lt_irrefl _ hs
  have hre : 1 ≤ s.re := hs.le
  have hev : LFunction (1 : DirichletCharacter ℂ q) =ᶠ[nhds s]
      fun z => (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) * riemannZeta z := by
    filter_upwards [isOpen_ne.mem_nhds hs1] with z hz
    exact LFunctionTrivChar_eq_mul_riemannZeta hz
  have hfac : ∀ p ∈ q.primeFactors, (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s ≠ 0 :=
    fun p hp => one_sub_ne_zero (Nat.prime_of_mem_primeFactors hp) hre
  have hdfac : ∀ p ∈ q.primeFactors, DifferentiableAt ℂ (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s :=
    fun p hp => (hasDerivAt_factor (Nat.prime_of_mem_primeFactors hp) s).differentiableAt
  have hF0 : (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hfac
  have hFd : DifferentiableAt ℂ (fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) s :=
    DifferentiableAt.fun_finsetProd hdfac
  have hζ0 : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hζd : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hL : deriv (LFunction (1 : DirichletCharacter ℂ q)) s /
      LFunction (1 : DirichletCharacter ℂ q) s =
      logDeriv (fun z => (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) * riemannZeta z) s := by
    rw [logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [hL, logDeriv_mul (f := fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) s hF0 hζ0
    hFd hζd, ← logDeriv_apply riemannZeta, add_sub_cancel_right,
    logDeriv_prod (f := fun (p : ℕ) (z : ℂ) => 1 - (p : ℂ) ^ (-z)) hfac hdfac]
  calc ‖∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖
      ≤ ∑ p ∈ q.primeFactors, ‖logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ q.primeFactors, Real.log p :=
        Finset.sum_le_sum fun p hp => norm_logDeriv_factor_le (Nat.prime_of_mem_primeFactors hp) hre
    _ ≤ Real.log q := sum_log_primeFactors_le q
end GlobalTheory.PrincipalLogDeriv
