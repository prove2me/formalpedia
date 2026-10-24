-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedSimplex_bounds_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T02:22:09.403061+00:00
-- url     : https://prove2.me/submissions/340cdb54-685f-4a00-bebc-40f6bf3787cb

import Mathlib

open Filter Topology
open scoped BigOperators

namespace PXTn

lemma lim (n : ℕ) (c K : ℝ) :
    Tendsto (fun H : ℝ => (H + c) ^ n / K / H ^ n) atTop (nhds (1 / K)) := by
  have h1 : Tendsto (fun H : ℝ => (1 + c * H⁻¹) ^ n / K) atTop (nhds ((1 + c * 0) ^ n / K)) :=
    ((tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_inv_atTop_zero)).pow n).div_const K
  simp only [mul_zero, add_zero, one_pow] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with H hH
  rw [div_div, mul_comm K, ← div_div, ← div_pow]
  congr 2
  field_simp

end PXTn

theorem solution
    (n : ℕ) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) :
    Tendsto (fun H : ℝ =>
      (H - ∑ i, w i) ^ n / ((n.factorial : ℝ) * ∏ i, w i) / H ^ n)
      atTop (nhds (1 / ((n.factorial : ℝ) * ∏ i, w i))) ∧
    Tendsto (fun H : ℝ =>
      (H + ∑ i, w i) ^ n / ((n.factorial : ℝ) * ∏ i, w i) / H ^ n)
      atTop (nhds (1 / ((n.factorial : ℝ) * ∏ i, w i))) := by
  refine ⟨?_, PXTn.lim n _ _⟩
  simpa [sub_eq_add_neg] using PXTn.lim n (-(∑ i, w i)) ((n.factorial : ℝ) * ∏ i, w i)
