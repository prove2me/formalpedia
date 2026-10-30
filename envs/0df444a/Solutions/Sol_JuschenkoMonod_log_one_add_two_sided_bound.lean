-- Prove2me | solution 1 for JuschenkoMonod.log_one_add_two_sided_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:32:05.964356+00:00
-- url     : https://prove2.me/submissions/ceb7f9f9-632e-4b87-a60e-cd4df79de8f5

import Mathlib

namespace JuschenkoMonod

theorem log_aux :
    0 < 4 * Real.log 2 - 2 ∧ ∀ z : ℝ, -1 / 2 ≤ z →
      z - (4 * Real.log 2 - 2) * z ^ 2 ≤ Real.log (1 + z) ∧ Real.log (1 + z) ≤ z := by
  have h2 := Real.log_two_gt_d9
  have hC : 0 < 4 * Real.log 2 - 2 := by linarith
  refine ⟨hC, fun z hz => ⟨?_, ?_⟩⟩
  · by_cases h0 : 0 ≤ z
    · -- z ≥ 0: log(1+z) ≥ z - z^2/2
      have key : ∀ y : ℝ, 0 ≤ y → y - y ^ 2 / 2 ≤ Real.log (1 + y) := by
        intro y hy
        let g : ℝ → ℝ := fun y => Real.log (1 + y) - y + y ^ 2 / 2
        have hmono : MonotoneOn g (Set.Ici 0) := by
          apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
          · intro x hx
            have : (0:ℝ) < 1 + x := by have := Set.mem_Ici.mp hx; linarith
            exact (((continuousAt_const.add continuousAt_id).log this.ne').sub continuousAt_id
              |>.add ((continuousAt_id.pow 2).div_const 2)).continuousWithinAt
          · intro x hx
            have hx' : 0 < x := by simpa using hx
            have : (0:ℝ) < 1 + x := by linarith
            have hd : DifferentiableAt ℝ g x := by
              apply DifferentiableAt.add
              · exact (DifferentiableAt.log (by fun_prop) this.ne').sub differentiableAt_id
              · fun_prop
            exact hd.differentiableWithinAt
          · intro x hx
            have hx' : 0 < x := by simpa using hx
            have : (0:ℝ) < 1 + x := by linarith
            have : deriv g x = x ^ 2 / (1 + x) := by
              have h1 : HasDerivAt g (1 / (1 + x) - 1 + x) x := by
                have a := ((hasDerivAt_id x).const_add 1).log this.ne'
                have b := a.sub (hasDerivAt_id x)
                have c := b.add ((hasDerivAt_pow 2 x).div_const 2)
                exact c.congr_deriv (by simp)
              rw [h1.deriv]; field_simp; ring
            rw [this]; positivity
        have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy) hy
        simp [g] at this
        linarith
      have := key z h0
      nlinarith [sq_nonneg z]
    · push_neg at h0
      set w := -z with hw
      have hw0 : 0 ≤ w := by linarith
      have hw1 : w ≤ 1 / 2 := by linarith
      have hs := Real.hasSum_pow_div_log_of_abs_lt_one (x := w) (by rw [abs_of_nonneg hw0]; linarith)
      have hs2 := Real.hasSum_pow_div_log_of_abs_lt_one (x := (1/2:ℝ)) (by norm_num [abs_of_pos])
      have hs' := (hasSum_nat_add_iff' 1).mpr hs
      have hs2' := (hasSum_nat_add_iff' 1).mpr hs2
      simp only [Finset.sum_range_one] at hs' hs2'
      have hs3 := hs2'.mul_left (4 * w ^ 2)
      have hle := by
        refine hasSum_le (fun n => ?_) hs' hs3
        show w ^ (n + 1 + 1) / ((n + 1 : ℕ) + 1) ≤ 4 * w ^ 2 * ((1/2:ℝ) ^ (n + 1 + 1) / ((n + 1 : ℕ) + 1))
        have : w ^ (n + 1 + 1) ≤ 4 * w ^ 2 * (1/2:ℝ) ^ (n + 1 + 1) := by
          have : w ^ n ≤ (1/2:ℝ) ^ n := pow_le_pow_left₀ hw0 hw1 n
          calc w ^ (n+1+1) = w ^ 2 * w ^ n := by ring
            _ ≤ w ^ 2 * (1/2) ^ n := by gcongr
            _ = 4 * w ^ 2 * (1/2:ℝ) ^ (n + 1 + 1) := by ring
        rw [← mul_div_assoc]
        gcongr
      have hl : Real.log (1 - 1/2 : ℝ) = - Real.log 2 := by
        rw [show (1 - 1/2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv]
      rw [hl] at hle
      have e : z = -w := by rw [hw]; ring
      rw [e, show (1 + -w) = 1 - w by ring]
      norm_num at hle
      nlinarith
  · have := Real.log_le_sub_one_of_pos (x := 1 + z) (by linarith)
    linarith

end JuschenkoMonod

theorem solution :
    0 < 4 * Real.log 2 - 2 ∧ ∀ z : ℝ, -1 / 2 ≤ z →
      z - (4 * Real.log 2 - 2) * z ^ 2 ≤ Real.log (1 + z) ∧ Real.log (1 + z) ≤ z :=
  JuschenkoMonod.log_aux
