-- Prove2me | solution 1 for GlobalTheory.KroneckerLimit.hasSum_eisenstein
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:16:45.649639+00:00
-- url     : https://prove2.me/submissions/8e98a298-b5f1-4289-9ad3-b296be74af7d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SummableAndAbsTsumSubIntegralLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole
import Theorems.Thm_GlobalTheory_KroneckerLimit_hasSum_lattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Set
open scoped Real
open GlobalTheory GlobalTheory.KroneckerLimit
namespace GlobalTheory.KroneckerLimit
theorem _root_.solution (τ : UpperHalfPlane) {s : ℝ} (hs : 1 < s) :
    HasSum (fun p : {p : ℤ × ℤ // p ≠ 0} =>
        τ.im ^ s / ‖(p.1.1 * τ + p.1.2 : ℂ)‖ ^ (2 * s))
      (τ.im ^ s * (rowSum 0 0 s + 2 * (∑' m, rowError τ.re τ.im m s))
        + 2 * (betaConst s * τ.im ^ (1 - s)) * ∑' n : ℕ, (n + 1 : ℝ) ^ (1 - 2 * s)) := by
  have hy := τ.im_pos
  have h := (hasSum_lattice τ.re hy hs).mul_left (τ.im ^ s)
  have e : τ.im ^ (1 - s) = τ.im ^ s * τ.im ^ (1 - 2 * s) := by
    rw [← Real.rpow_add hy]; congr 1; ring
  have h' := (hasSum_subtype_iff_of_support_subset (s := {p : ℤ × ℤ | p ≠ 0}) (by
    intro p hp h0
    apply hp
    simp [h0, Real.zero_rpow (show -s ≠ 0 by linarith)])).2 h
  rw [mul_add (τ.im ^ s), show ∀ a b c d : ℝ, a * (2 * (b * c) * d) = 2 * (b * (a * c)) * d by
    intros; ring, ← e] at h'
  refine h'.congr_fun (fun p => ?_)
  · rw [show 2 * s = ((2 : ℕ) : ℝ) * s by norm_num, Real.rpow_natCast_mul (norm_nonneg _),
      Complex.sq_norm, Complex.normSq_apply, Function.comp_apply,
      Real.rpow_neg (by positivity), div_eq_mul_inv]
    simp [sq]
end GlobalTheory.KroneckerLimit
