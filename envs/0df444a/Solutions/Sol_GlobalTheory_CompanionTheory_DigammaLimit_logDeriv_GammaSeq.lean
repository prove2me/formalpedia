-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DigammaLimit.logDeriv_GammaSeq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:26:24.303164+00:00
-- url     : https://prove2.me/submissions/920991c2-2e3c-45d9-a45c-d1e5c4ea3768

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaTendstoLogSubHarmonic
import Theorems.Thm_GlobalTheory_CompanionTheory_DigammaLimit_add_natCast_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Metric Set
open scoped Nat Real
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DigammaLimit
namespace GlobalTheory.CompanionTheory.DigammaLimit
theorem _root_.solution {z : ℂ} (hz : 0 < z.re) {n : ℕ} (hn : n ≠ 0) :
    logDeriv (fun w => GammaSeq w n) z =
      ((Real.log n : ℝ) : ℂ) - ∑ k ∈ Finset.range (n + 1), 1 / (z + (k : ℂ)) := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hP : ∀ j ∈ Finset.range (n + 1), z + (j : ℂ) ≠ 0 := fun j _ => add_natCast_ne_zero hz j
  have hd1 : HasDerivAt (fun w : ℂ => (n : ℂ) ^ w) ((n : ℂ) ^ z * Complex.log n * 1) z :=
    (hasDerivAt_id z).const_cpow (Or.inl hn')
  have hfac : ((n ! : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  have hcp : (n : ℂ) ^ z ≠ 0 := by simp [Complex.cpow_eq_zero_iff, hn']
  have hd2 : DifferentiableAt ℂ (fun w : ℂ => ∏ j ∈ Finset.range (n + 1), (w + (j : ℂ))) z :=
    DifferentiableAt.fun_finset_prod fun j _ => by fun_prop
  have e1 : (fun w => GammaSeq w n) =
      fun w => ((n : ℂ) ^ w * (n ! : ℂ)) / ∏ j ∈ Finset.range (n + 1), (w + (j : ℂ)) := rfl
  have l1 : logDeriv (fun w : ℂ => (n : ℂ) ^ w) z = Complex.log n := by
    rw [logDeriv_apply, hd1.deriv]
    field_simp
  have l2 : ∀ j : ℕ, logDeriv (fun w : ℂ => w + (j : ℂ)) z = 1 / (z + (j : ℂ)) := by
    intro j
    rw [logDeriv_apply]
    simp
  rw [e1, logDeriv_div (f := fun w : ℂ => (n : ℂ) ^ w * (n ! : ℂ))
      (g := fun w : ℂ => ∏ j ∈ Finset.range (n + 1), (w + (j : ℂ))) z
      (mul_ne_zero hcp hfac) (Finset.prod_ne_zero_iff.2 hP)
      (hd1.differentiableAt.mul_const _) hd2,
    logDeriv_mul (f := fun w : ℂ => (n : ℂ) ^ w) (g := fun _ : ℂ => (n ! : ℂ)) z hcp hfac
      hd1.differentiableAt (differentiableAt_const _),
    logDeriv_prod (f := fun (j : ℕ) (w : ℂ) => w + (j : ℂ)) hP (fun j _ => by fun_prop),
    l1, logDeriv_const, Pi.zero_apply, add_zero, Complex.natCast_log]
  simp only [l2]
end GlobalTheory.CompanionTheory.DigammaLimit
