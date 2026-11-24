-- Prove2me | solution 1 for GlobalTheory.ExpDivision.dioph
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:44:37.937205+00:00
-- url     : https://prove2.me/submissions/afa21a88-5c0d-4569-b8cb-0762028f9746

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityAsSumExpMinusOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory GlobalTheory.ExpDivision
namespace GlobalTheory.ExpDivision
theorem _root_.solution (t : ℝ) (hp : round t ≠ 0) :
    1 ≤ 6 * (1 + |t|) * (|t - round t| + |√2 * t - round (√2 * t)|) := by
  set p := round t with hpdef
  set q := round (√2 * t) with hqdef
  have h1 : |t - p| ≤ 1 / 2 := abs_sub_round t
  have h2 : |√2 * t - q| ≤ 1 / 2 := abs_sub_round _
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 < √2 := by positivity
  have hs2 : √2 ≤ 3 / 2 := by nlinarith
  have hne : (2 * p ^ 2 - q ^ 2 : ℤ) ≠ 0 := by
    intro h
    have hr : (2 : ℝ) * p ^ 2 - q ^ 2 = 0 := by exact_mod_cast h
    have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp
    have : (√2 * p - q) * (√2 * p + q) = 0 := by nlinarith
    have hirr := irrational_sqrt_two
    rcases mul_eq_zero.1 this with h' | h'
    · exact hirr ⟨(q : ℚ) / p, by push_cast; field_simp; linarith⟩
    · exact hirr ⟨-(q : ℚ) / p, by push_cast; field_simp; linarith⟩
  have h3 : (1 : ℝ) ≤ |(2 : ℝ) * p ^ 2 - q ^ 2| := by
    have := Int.one_le_abs hne
    exact_mod_cast this
  have h4 : (2 : ℝ) * p ^ 2 - q ^ 2 = (√2 * p - q) * (√2 * p + q) := by nlinarith
  rw [h4, abs_mul] at h3
  have h5 : |√2 * p - q| ≤ 2 * (|t - p| + |√2 * t - q|) := by
    have : √2 * p - q = (√2 * t - q) - √2 * (t - p) := by ring
    rw [this]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_pos hs0]
    nlinarith [abs_nonneg (t - p), abs_nonneg (√2 * t - q)]
  have h6 : |√2 * p + q| ≤ 3 * (1 + |t|) := by
    have : √2 * p + q = 2 * √2 * t - (√2 * t - q) - √2 * (t - p) := by ring
    rw [this]
    refine (abs_sub _ _).trans ?_
    have := abs_sub (2 * √2 * t) (√2 * t - q)
    rw [abs_mul, abs_mul, abs_of_pos hs0, abs_two] at this
    rw [abs_mul, abs_of_pos hs0]
    nlinarith [abs_nonneg (t - p), abs_nonneg t]
  calc (1 : ℝ) ≤ _ := h3
    _ ≤ (2 * (|t - p| + |√2 * t - q|)) * (3 * (1 + |t|)) := by gcongr
    _ = _ := by ring
end GlobalTheory.ExpDivision
