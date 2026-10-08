-- Prove2me | solution 1 for OAI.PiExponent.two_mem_approximationExponents
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-07T07:07:39.717982+00:00
-- url     : https://prove2.me/submissions/ea769243-783f-43ab-9a89-ef1793c87b54

import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Theorems.Thm_OAI_PiExponent_finite_rat_den_le_abs_sub_lt_one

namespace OAI

namespace PiExponent

 













end PiExponent

end OAI

open OAI.PiExponent in
theorem solution {x : ℝ} (hx : Irrational x) :
    (2 : ℝ) ∈ ApproximationExponents x := by
  refine ⟨by norm_num, ?_⟩
  have hi := Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hx
  have hf := finite_rat_den_le_abs_sub_lt_one x 1
  apply (hi.sdiff hf).mono
  intro r hr
  have hrden : 1 ≤ (r.den : ℝ) := by exact_mod_cast r.pos
  have hrone : |x - (r : ℝ)| < 1 :=
    hr.1.trans_le (by
      simpa only [div_one] using
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
          (by nlinarith : (1 : ℝ) ≤ (r.den : ℝ)^2))
  have hr2 : 2 ≤ r.den := by
    by_contra h
    exact hr.2 ⟨by omega, hrone⟩
  refine ⟨hr2, abs_pos.mpr (sub_ne_zero.mpr (hx.ne_rat r)), ?_⟩
  simpa only [Set.mem_ofPred_eq, Real.rpow_neg (Nat.cast_nonneg r.den),
    Real.rpow_two, one_div] using hr.1
