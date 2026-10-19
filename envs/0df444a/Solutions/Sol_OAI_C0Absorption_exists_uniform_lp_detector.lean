-- Prove2me | solution 1 for OAI.C0Absorption.exists_uniform_lp_detector
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:04:22.427555+00:00
-- url     : https://prove2.me/submissions/883e5492-c6ea-46be-a085-1dcf1851e08d

import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists

open OAI OAI.C0Absorption
open scoped BigOperators NNReal ENNReal
open Finset


theorem solution (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp : 0 < p.toReal) (hq : 0 < q.toReal) (hqp : q.toReal < p.toReal)
    (a B : ℝ) (ha : 0 < a) (hB : 0 < B) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (x : Fin n → ℝ),
      a ≤ ‖WithLp.toLp p x‖ → ‖WithLp.toLp q x‖ ≤ B →
      ∃ i, δ < |x i| := by
  set P := p.toReal with hPdef
  set Q := q.toReal with hQdef
  have hPQ : 0 < P - Q := by linarith
  have hnorm : ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], 0 < r.toReal → ∀ (n : ℕ) (x : Fin n → ℝ),
      ∑ i, |x i| ^ r.toReal = ‖WithLp.toLp r x‖ ^ r.toReal := by
    intro r _ hr n x
    rw [PiLp.norm_eq_sum hr, one_div, Real.rpow_inv_rpow (Finset.sum_nonneg (fun i _ => by positivity)) hr.ne']
    simp [Real.norm_eq_abs]
  set c := a ^ P / (2 * B ^ Q) with hc
  have hcpos : 0 < c := by positivity
  refine ⟨c ^ (1 / (P - Q)), by positivity, ?_⟩
  intro n x hxa hxB
  by_contra hcon
  push_neg at hcon
  have hδ : (c ^ (1 / (P - Q))) ^ (P - Q) = c := by
    rw [← Real.rpow_mul hcpos.le, one_div_mul_cancel hPQ.ne', Real.rpow_one]
  have hpt : ∀ i, |x i| ^ P ≤ |x i| ^ Q * c := by
    intro i
    have e : |x i| ^ P = |x i| ^ Q * |x i| ^ (P - Q) := by
      rw [← Real.rpow_add' (abs_nonneg _) (by linarith)]; ring_nf
    rw [e, ← hδ]
    gcongr
    exact hcon i
  have hsum : ∑ i, |x i| ^ P ≤ (∑ i, |x i| ^ Q) * c := by
    rw [Finset.sum_mul]; exact Finset.sum_le_sum (fun i _ => hpt i)
  rw [hnorm p hp, hnorm q hq] at hsum
  have h1 : a ^ P ≤ ‖WithLp.toLp p x‖ ^ P := Real.rpow_le_rpow ha.le hxa hp.le
  have h2 : ‖WithLp.toLp q x‖ ^ Q ≤ B ^ Q := Real.rpow_le_rpow (norm_nonneg _) hxB hq.le
  have h3 : ‖WithLp.toLp q x‖ ^ Q * c ≤ B ^ Q * c := mul_le_mul_of_nonneg_right h2 hcpos.le
  have h4 : B ^ Q * c = a ^ P / 2 := by
    rw [hc]; have : 0 < B ^ Q := by positivity
    field_simp
  have : 0 < a ^ P := by positivity
  linarith

