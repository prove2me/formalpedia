-- Prove2me | solution 1 for GivenDegreeSeq.MLE.x0_sub_x1_at_beta
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T04:26:56.034768+00:00
-- url     : https://prove2.me/submissions/41b23c2e-dbed-4e7c-89dd-69e119e98c1b

import Mathlib
import Definitions.Def_GivenDegreeSeq_MLE_Basic

open GivenDegreeSeq.MLE in
theorem solution (n : ℕ) (hn : 2 ≤ n) (d : Fin n → ℝ) (hd : ∀ i, 0 < d i)
    (β : Fin n → ℝ) (i : Fin n) :
    (β - GivenDegreeSeq.FixedPoint.phi d β) i = Real.log (dbar β i / d i) := by
  have hrpos : ∀ j, 0 < GivenDegreeSeq.FixedPoint.r β i j := by
    intro j
    unfold GivenDegreeSeq.FixedPoint.r
    positivity
  have hne : (Finset.univ.erase i).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
    omega
  have hS : 0 < ∑ j ∈ Finset.univ.erase i, GivenDegreeSeq.FixedPoint.r β i j :=
    Finset.sum_pos (fun j _ => hrpos j) hne
  have hedge : ∀ j, GivenDegreeSeq.FixedPoint.edgeProb β i j =
      Real.exp (β i) * GivenDegreeSeq.FixedPoint.r β i j := by
    intro j
    unfold GivenDegreeSeq.FixedPoint.edgeProb GivenDegreeSeq.FixedPoint.r
    rw [Real.exp_add, Real.exp_neg]
    have h1 : 0 < Real.exp (β i) := Real.exp_pos _
    have h2 : 0 < Real.exp (β j) := Real.exp_pos _
    field_simp
  have hdbar : dbar β i = Real.exp (β i) *
      ∑ j ∈ Finset.univ.erase i, GivenDegreeSeq.FixedPoint.r β i j := by
    unfold dbar
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => hedge j)
  rw [Pi.sub_apply, hdbar]
  unfold GivenDegreeSeq.FixedPoint.phi
  rw [Real.log_div (by positivity) (hd i).ne', Real.log_mul (Real.exp_pos _).ne' hS.ne',
    Real.log_exp]
  ring
