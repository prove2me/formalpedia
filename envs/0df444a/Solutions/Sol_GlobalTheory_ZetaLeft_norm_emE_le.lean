-- Prove2me | solution 1 for GlobalTheory.ZetaLeft.norm_emE_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:30:35.31711+00:00
-- url     : https://prove2.me/submissions/8cd3b68f-fae5-4563-b497-27ddf1c48308

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormSubOneMulRiemannZetaLe
import Theorems.Thm_GlobalTheory_ZetaLeft_hasDerivAt_shift_cpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Filter Topology
open GlobalTheory GlobalTheory.ZetaLeft
namespace GlobalTheory.ZetaLeft
theorem _root_.solution {a : ℝ} (ha : 1 ≤ a) {s : ℂ} (hs : -(15/8 : ℝ) ≤ s.re) :
    ‖emE a s‖ ≤ (‖s‖ + 2) ^ 4 * a ^ (-(9/8 : ℝ)) := by
  set w : ℂ := 1 - s with hw
  let G : ℂ → ℂ := fun z => ((a : ℂ) + z) ^ w - (z - 1/2) * (w * ((a : ℂ) + z) ^ (w - 1))
    + (z ^ 2 - z + 1/6) / 2 * (w * (w - 1) * ((a : ℂ) + z) ^ (w - 1 - 1))
    - (z ^ 3 - 3/2 * z ^ 2 + z / 2) / 6 * (w * (w - 1) * (w - 1 - 1) * ((a : ℂ) + z) ^ (w - 1 - 1 - 1))
  let G' : ℝ → ℂ := fun t => - (((t : ℂ) ^ 3 - 3/2 * t ^ 2 + t / 2) / 6) *
    (w * (w - 1) * (w - 1 - 1) * (w - 1 - 1 - 1) * ((a : ℂ) + t) ^ (w - 1 - 1 - 1 - 1))
  have hd : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun y : ℝ => G y) (G' t) t := by
    intro t ht
    have h : 0 < a + t := by linarith
    have p1 : HasDerivAt (fun z : ℂ => z - 1/2) 1 (t : ℂ) := (hasDerivAt_id _).sub_const _
    have p2 : HasDerivAt (fun z : ℂ => (z ^ 2 - z + 1/6) / 2) ((t : ℂ) - 1/2) (t : ℂ) := by
      have := ((((hasDerivAt_id (t : ℂ)).pow 2).sub (hasDerivAt_id _)).add_const (1/6)).div_const 2
      exact this.congr_deriv (by simp; ring)
    have p3 : HasDerivAt (fun z : ℂ => (z ^ 3 - 3/2 * z ^ 2 + z / 2) / 6)
        (((t : ℂ) ^ 2 - t + 1/6) / 2) (t : ℂ) := by
      have := ((((hasDerivAt_id (t : ℂ)).pow 3).sub
        (((hasDerivAt_id (t : ℂ)).pow 2).const_mul (3/2))).add
        ((hasDerivAt_id (t : ℂ)).div_const 2)).div_const 6
      exact this.congr_deriv (by simp; ring)
    have hG : HasDerivAt G (G' t) (t : ℂ) := by
      have := (((hasDerivAt_shift_cpow h w).sub
        (p1.mul ((hasDerivAt_shift_cpow h (w - 1)).const_mul w))).add
        (p2.mul ((hasDerivAt_shift_cpow h (w - 1 - 1)).const_mul (w * (w - 1))))).sub
        (p3.mul ((hasDerivAt_shift_cpow h (w - 1 - 1 - 1)).const_mul (w * (w - 1) * (w - 1 - 1))))
      exact this.congr_deriv (by simp only [G']; ring)
    exact hG.comp_ofReal
  have hb : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖G' t‖ ≤ (‖s‖ + 2) ^ 4 * a ^ (-(9/8 : ℝ)) := by
    intro t ht
    have h : 0 < a + t := by linarith [ht.1]
    have b1 : ‖- (((t : ℂ) ^ 3 - 3/2 * t ^ 2 + t / 2) / 6)‖ ≤ 1 := by
      have : - (((t : ℂ) ^ 3 - 3/2 * t ^ 2 + t / 2) / 6)
          = ((- ((t ^ 3 - 3/2 * t ^ 2 + t / 2) / 6) : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
      have h2 : t ^ 2 ≤ 1 := pow_le_one₀ ht.1 ht.2.le
      have h3 : t ^ 3 ≤ 1 := pow_le_one₀ ht.1 ht.2.le
      have h4 : 0 ≤ t ^ 2 := by positivity
      have h5 : 0 ≤ t ^ 3 := pow_nonneg ht.1 _
      constructor <;> linarith [ht.1, ht.2]
    have key : ∀ c : ℝ, |c| ≤ 2 → ‖(c : ℂ) - s‖ ≤ ‖s‖ + 2 := by
      intro c hc
      have := norm_sub_le (c : ℂ) s
      rw [Complex.norm_real, Real.norm_eq_abs] at this
      linarith
    have c0 : ‖w‖ ≤ ‖s‖ + 2 := by simpa using key 1 (by norm_num)
    have c1 : ‖w - 1‖ ≤ ‖s‖ + 2 := by
      convert key 0 (by norm_num) using 2; rw [hw]; push_cast; ring
    have c2 : ‖w - 1 - 1‖ ≤ ‖s‖ + 2 := by
      convert key (-1) (by norm_num) using 2; rw [hw]; push_cast; ring
    have c3 : ‖w - 1 - 1 - 1‖ ≤ ‖s‖ + 2 := by
      convert key (-2) (by norm_num) using 2; rw [hw]; push_cast; ring
    have c4 : ‖((a : ℂ) + t) ^ (w - 1 - 1 - 1 - 1)‖ ≤ a ^ (-(9/8 : ℝ)) := by
      rw [← Complex.ofReal_add, Complex.norm_cpow_eq_rpow_re_of_pos h]
      have e : (w - 1 - 1 - 1 - 1).re ≤ -(9/8 : ℝ) := by
        simp [hw]; linarith
      calc _ ≤ (a + t) ^ (-(9/8 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [ht.1]) e
        _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith [ht.1]) (by norm_num)
    simp only [G', norm_mul]
    calc _ ≤ 1 * ((‖s‖ + 2) * (‖s‖ + 2) * (‖s‖ + 2) * (‖s‖ + 2) * a ^ (-(9/8 : ℝ))) := by
          gcongr
      _ = _ := by ring
  have := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := fun y : ℝ => G y) (f' := G')
    (fun t ht => (hd t ht.1).hasDerivWithinAt) hb
  refine le_of_eq_of_le (congrArg _ ?_) this
  simp only [G, emE, emT, ← hw]
  push_cast
  simp only [add_zero]
  ring
end GlobalTheory.ZetaLeft
