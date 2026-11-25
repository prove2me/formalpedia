-- Prove2me | solution 1 for Newton.young_exponent_to_three_holder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:28:43.536389+00:00
-- url     : https://prove2.me/submissions/abb51fdc-3fff-4f53-852e-0c572e7817da

import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.MetricSpace.Holder
import Definitions.Def_Newton_MeasureTheory_Integral_Tonelli
import Definitions.Def_Newton_Analysis_Convolution_Auxiliary
import Theorems.Thm_Newton_young_exponent_p_le_r
import Theorems.Thm_Newton_young_exponent_q_le_r
import Theorems.Thm_Newton_ennreal_sub_div_mul

set_option autoImplicit false
open MeasureTheory Complex NNReal
open scoped ENNReal Topology ContDiff ComplexConjugate
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution
    {p q r : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hp_ne_top : p ≠ ⊤) (hq_ne_top : q ≠ ⊤) (hr_ne_top : r ≠ ⊤)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r) :
    1/r + (r-p)/(p*r) + (r-q)/(q*r) = 1 := by
  -- p, q, r are positive and finite
  have hp_pos : p ≠ 0 := (one_pos.trans_le hp).ne'
  have hq_pos : q ≠ 0 := (one_pos.trans_le hq).ne'
  have hr_pos : r ≠ 0 := (one_pos.trans_le hr).ne'
  -- From the Young exponent condition we know p ≤ r and q ≤ r
  have h_p_le_r : p ≤ r := young_exponent_p_le_r hq hpqr
  have h_q_le_r : q ≤ r := young_exponent_q_le_r hp hpqr
  -- Rewrite the auxiliary exponents (r-p)/(p*r) and (r-q)/(q*r)
  -- using the identities (r-p)/(p*r) = 1/p - 1/r and (r-q)/(q*r) = 1/q - 1/r.
  have h1 : (r - p) / (p * r) = 1/p - 1/r :=
    ennreal_sub_div_mul hp_pos hp_ne_top hr_pos hr_ne_top
  have h2 : (r - q) / (q * r) = 1/q - 1/r :=
    ennreal_sub_div_mul hq_pos hq_ne_top hr_pos hr_ne_top
  -- The fractions 1/p, 1/q, 1/r are all finite.
  have h_one_div_p_ne_top : 1/p ≠ ⊤ := ENNReal.div_ne_top ENNReal.one_ne_top hp_pos
  have h_one_div_q_ne_top : 1/q ≠ ⊤ := ENNReal.div_ne_top ENNReal.one_ne_top hq_pos
  have h_one_div_r_ne_top : 1/r ≠ ⊤ := ENNReal.div_ne_top ENNReal.one_ne_top hr_pos
  -- From p ≤ r and q ≤ r we also have 1/r ≤ 1/p and 1/r ≤ 1/q.
  have h_one_div_r_le_one_div_p : 1/r ≤ 1/p := by
    rw [one_div, one_div, ENNReal.inv_le_inv]
    exact h_p_le_r
  have h_one_div_r_le_one_div_q : 1/r ≤ 1/q := by
    rw [one_div, one_div, ENNReal.inv_le_inv]
    exact h_q_le_r
  -- First simplify 1/r + (1/p - 1/r).
  have step1 : 1/r + (1/p - 1/r) = 1/p :=
    add_tsub_cancel_of_le h_one_div_r_le_one_div_p
  -- Next, rewrite 1/p + (1/q - 1/r) as 1/p + 1/q - 1/r using cancellability
  -- of addition by the finite element 1/r.
  have hc : AddLECancellable (1/r : ℝ≥0∞) :=
    ENNReal.cancel_of_ne h_one_div_r_ne_top
  have step2' : 1/p + 1/q - 1/r = 1/p + (1/q - 1/r) :=
    hc.add_tsub_assoc_of_le h_one_div_r_le_one_div_q (1/p)
  have step2 : 1/p + (1/q - 1/r) = 1/p + 1/q - 1/r :=
    step2'.symm
  -- Finally, use the Young exponent condition to evaluate 1/p + 1/q - 1/r.
  have step3 : 1/p + 1/q - 1/r = 1 := by
    -- From 1/p + 1/q = 1 + 1/r and finiteness of 1/r.
    have := ENNReal.sub_eq_of_eq_add (a := 1/p + 1/q)
        (b := 1/r) (c := (1 : ℝ≥0∞)) h_one_div_r_ne_top hpqr
    simpa using this
  -- Intermediate simplification of the left-hand side.
  have step0 :
      1/r + (r-p)/(p*r) + (r-q)/(q*r) =
        1/r + (1/p - 1/r) + (1/q - 1/r) := by
    simp [h1, h2]
  have step_mid :
      1/r + (1/p - 1/r) + (1/q - 1/r) =
        1/p + (1/q - 1/r) := by
    -- add (1/q - 1/r) to both sides of step1
    have h := congrArg (fun x : ℝ≥0∞ => x + (1/q - 1/r)) step1
    -- rewrite using associativity and commutativity of addition
    simpa [add_comm, add_left_comm, add_assoc] using h
  -- Put everything together.
  calc
    1/r + (r-p)/(p*r) + (r-q)/(q*r)
        = 1/r + (1/p - 1/r) + (1/q - 1/r) := step0
    _   = 1/p + (1/q - 1/r) := step_mid
    _   = 1/p + 1/q - 1/r := step2
    _   = 1 := step3
end Newton
