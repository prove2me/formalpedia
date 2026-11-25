-- Prove2me | solution 1 for GlobalTheory.PrincipalLogDeriv.neg_re_logDeriv_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:55:35.865605+00:00
-- url     : https://prove2.me/submissions/1ccef323-eb5d-472d-9fcc-b0b3c8b8ea2b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivRiemannZetaLocalZeroSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NegReLogDerivPrincipalLFunctionLe
import Theorems.Thm_GlobalTheory_PrincipalLogDeriv_norm_logDeriv_sub_le
import Theorems.Thm_GlobalTheory_T_logDeriv_riemannZeta_local_zero_sum


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
theorem _root_.solution : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (σ t : ℝ), 1 < σ → σ ≤ 2 → -(deriv (LFunction (1 : DirichletCharacter ℂ q)) (σ + t * I) / LFunction (1 : DirichletCharacter ℂ q) (σ + t * I)).re ≤ (1 / ((σ : ℂ) + t * I - 1)).re + C * Real.log (q * (|t| + 2)) := by
  obtain ⟨C, hC, hZ⟩ := GlobalTheory.T.logDeriv_riemannZeta_local_zero_sum
  refine ⟨C + 1, by linarith, ?_⟩
  intro q _ σ t hσ1 hσ2
  set s : ℂ := (σ : ℂ) + t * I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  have hs1 : 1 < s.re := by rw [hsre]; exact hσ1
  have hsne : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs1
    exact lt_irrefl _ hs1
  have hζ0 : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs1
  have hdist : ‖s - (3 / 2 + t * I)‖ ≤ 2 / 3 := by
    have h1 : s - (3 / 2 + t * I) = ((σ - 3 / 2 : ℝ) : ℂ) := by
      rw [hsdef]; push_cast; ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  obtain ⟨hfin, hbound⟩ := hZ t s hdist hsne hζ0
  set Z := {w : ℂ | ‖w - (3 / 2 + t * I)‖ ≤ 5 / 6 ∧ w ≠ 1 ∧ riemannZeta w = 0} with hZdef
  set S := ∑ᶠ w ∈ Z, (analyticOrderNatAt riemannZeta w : ℂ) / (s - w) with hSdef
  have hterm : ∀ w ∈ Z, 0 ≤ ((analyticOrderNatAt riemannZeta w : ℂ) / (s - w)).re := by
    intro w hw
    have hw1 : w.re ≤ 1 := by
      by_contra h
      push Not at h
      exact riemannZeta_ne_zero_of_one_lt_re h hw.2.2
    have hpos : 0 ≤ (s - w).re := by rw [Complex.sub_re, hsre]; linarith
    rw [Complex.div_re]
    simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, zero_div, add_zero]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hpos) (Complex.normSq_nonneg _)
  have hS : 0 ≤ S.re := by
    rw [hSdef, finsum_mem_eq_finite_toFinset_sum _ hfin, Complex.re_sum]
    exact Finset.sum_nonneg fun w hw => hterm w (hfin.mem_toFinset.mp hw)
  set E := deriv riemannZeta s / riemannZeta s + 1 / (s - 1) - S with hEdef
  have hζ : deriv riemannZeta s / riemannZeta s = E - 1 / (s - 1) + S := by
    rw [hEdef]; ring
  have hE : -E.re ≤ C * Real.log (|t| + 2) :=
    le_trans (neg_le_abs _) (le_trans (Complex.abs_re_le_norm E) hbound)
  set D := deriv (LFunction (1 : DirichletCharacter ℂ q)) s / LFunction (1 : DirichletCharacter ℂ q) s
    - deriv riemannZeta s / riemannZeta s with hDdef
  have hD : ‖D‖ ≤ Real.log q := norm_logDeriv_sub_le q hs1
  have hDre : -D.re ≤ Real.log q := le_trans (neg_le_abs _) (le_trans (Complex.abs_re_le_norm D) hD)
  have hLsplit : deriv (LFunction (1 : DirichletCharacter ℂ q)) s /
      LFunction (1 : DirichletCharacter ℂ q) s = D + (E - 1 / (s - 1) + S) := by
    rw [hDdef, ← hζ]; ring
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have ht2 : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  have hlt : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith)
  have hlog : Real.log (q * (|t| + 2)) = Real.log q + Real.log (|t| + 2) :=
    Real.log_mul (by linarith) (by linarith)
  rw [hLsplit, hlog]
  simp only [Complex.add_re, Complex.sub_re]
  nlinarith
end GlobalTheory.PrincipalLogDeriv
