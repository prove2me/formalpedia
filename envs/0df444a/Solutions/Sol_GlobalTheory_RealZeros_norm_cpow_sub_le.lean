-- Prove2me | solution 1 for GlobalTheory.RealZeros.norm_cpow_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:54:06.700148+00:00
-- url     : https://prove2.me/submissions/a2946b28-14c8-4e06-a398-efc6cf064a67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RiemannZetaNeZeroOfMemIoo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
open GlobalTheory GlobalTheory.RealZeros
namespace GlobalTheory.RealZeros
theorem _root_.solution {s : ℂ} (hs : 0 < s.re) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ‖(a : ℂ) ^ (-s) - (b : ℂ) ^ (-s)‖ ≤ ‖s‖ * a ^ (-s.re - 1) * (b - a) := by
  have hs0 : -s ≠ 0 := by
    intro h
    have : s = 0 := neg_eq_zero.mp h
    simp [this] at hs
  have key := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun x : ℝ => (x : ℂ) ^ (-s))
    (f' := fun x : ℝ => (-s) * (x : ℂ) ^ (-s - 1)) (a := a) (b := b)
    (C := ‖s‖ * a ^ (-s.re - 1))
    (fun x hx => (hasDerivAt_ofReal_cpow_const (ne_of_gt (lt_of_lt_of_le ha hx.1)) hs0).hasDerivWithinAt)
    (fun x hx => by
      have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
      rw [norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos hx0]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have : (-s - 1).re = -s.re - 1 := by simp
      rw [this]
      exact Real.rpow_le_rpow_of_nonpos ha hx.1 (by linarith))
    b ⟨hab, le_rfl⟩
  rwa [norm_sub_rev] at key
end GlobalTheory.RealZeros
