-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DigammaLimit.euler_seq_le_Gamma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:26:23.246955+00:00
-- url     : https://prove2.me/submissions/9ae63d97-acc1-4ce4-a6ec-16683ffc22a7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaTendstoLogSubHarmonic

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
theorem _root_.solution {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) :
    (n : ℝ) ^ x * (n ! : ℝ) / ∏ j ∈ Finset.range (n + 1), (x + (j : ℝ)) ≤ Real.Gamma x := by
  have hfe : ∀ {y : ℝ}, 0 < y →
      (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
    intro y hy
    simp only [Function.comp]
    rw [Real.Gamma_add_one hy.ne', Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne', add_comm]
  have h := Real.BohrMollerup.ge_logGammaSeq (f := Real.log ∘ Real.Gamma)
    Real.convexOn_log_Gamma hfe hx hn
  have hf1 : (Real.log ∘ Real.Gamma) 1 = 0 := by simp [Real.Gamma_one]
  rw [hf1, zero_add] at h
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have hfac : (0 : ℝ) < (n ! : ℝ) := by positivity
  have hP : ∀ j ∈ Finset.range (n + 1), (0 : ℝ) < x + j := fun j _ => by positivity
  have hPpos : 0 < ∏ j ∈ Finset.range (n + 1), (x + (j : ℝ)) := Finset.prod_pos hP
  have hlog : Real.log ((n : ℝ) ^ x * (n ! : ℝ) / ∏ j ∈ Finset.range (n + 1), (x + (j : ℝ))) =
      Real.BohrMollerup.logGammaSeq x n := by
    rw [Real.log_div (by positivity) hPpos.ne', Real.log_mul (by positivity) hfac.ne',
      Real.log_rpow hn0, Real.log_prod (fun j hj => (hP j hj).ne')]
    rfl
  rw [← hlog] at h
  exact (Real.log_le_log_iff (by positivity) (Real.Gamma_pos_of_pos hx)).1 h
end GlobalTheory.CompanionTheory.DigammaLimit
