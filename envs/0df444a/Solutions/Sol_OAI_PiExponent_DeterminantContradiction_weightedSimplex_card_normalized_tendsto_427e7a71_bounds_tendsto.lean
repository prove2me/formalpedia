-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_normalized_tendsto_427e7a71_bounds_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T02:22:18.444868+00:00
-- url     : https://prove2.me/submissions/47eaa23a-a8dd-41e2-8a4c-921a153cc640

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
    (n : Nat) (w : Fin n -> Real) (hw : forall i, 0 < w i) :
    And
      (Tendsto (fun H : Real =>
        (H - Finset.univ.sum w) ^ n / ((n.factorial : Real) * Finset.univ.prod w) / H ^ n)
        atTop (nhds (1 / ((n.factorial : Real) * Finset.univ.prod w))))
      (Tendsto (fun H : Real =>
        (H + Finset.univ.sum w) ^ n / ((n.factorial : Real) * Finset.univ.prod w) / H ^ n)
        atTop (nhds (1 / ((n.factorial : Real) * Finset.univ.prod w)))) := by
  refine ⟨?_, PXTn.lim n _ _⟩
  simpa [sub_eq_add_neg] using PXTn.lim n (-(Finset.univ.sum w)) ((n.factorial : ℝ) * Finset.univ.prod w)
