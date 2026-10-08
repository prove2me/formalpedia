-- Prove2me | solution 1 for OAI.PiExponent.irrationalityExponent_eq_two_of_eventualLowerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-07T07:03:47.598651+00:00
-- url     : https://prove2.me/submissions/bf623eb4-230e-45f9-b474-2a87e9a97e71

import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Theorems.Thm_OAI_PiExponent_finite_rat_den_le_abs_sub_lt_one

namespace OAI

namespace PiExponent

 



theorem two_mem_approximationExponents {x : ℝ} (hx : Irrational x) :
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

theorem finite_goodRationalApproximations_of_eventualLowerBound {x ν : ℝ}
    (hx : EventualLowerBound x) (hν : 2 < ν) :
    (GoodRationalApproximations x ν).Finite := by
  obtain ⟨Q, hQ, hb⟩ := hx ν hν
  apply (finite_rat_den_le_abs_sub_lt_one x Q).subset
  intro r hr
  have hltQ : r.den < Q := by
    by_contra h
    have h := hb r.num r.den (by omega)
    rw [← Rat.cast_def] at h
    exact (not_lt_of_ge h) hr.2.2
  refine ⟨hltQ.le, hr.2.2.trans_le ?_⟩
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast r.pos) (by linarith)







end PiExponent

end OAI

open OAI.PiExponent in
theorem solution {x : ℝ}
    (hi : Irrational x) (hx : EventualLowerBound x) :
    irrationalityExponent x = 2 := by
  have htwo := two_mem_approximationExponents hi
  have hbound : ∀ ν ∈ ApproximationExponents x, ν ≤ 2 := by
    intro ν hν
    by_contra h
    exact (finite_goodRationalApproximations_of_eventualLowerBound hx (by linarith)).not_infinite hν.2
  apply le_antisymm
  · exact csSup_le ⟨2, htwo⟩ hbound
  · exact le_csSup ⟨2, hbound⟩ htwo
