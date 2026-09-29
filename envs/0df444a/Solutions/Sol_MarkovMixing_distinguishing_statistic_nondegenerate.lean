-- Prove2me | solution 1 for MarkovMixing.distinguishing_statistic_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-22T20:13:15.724841+00:00
-- url     : https://prove2.me/submissions/c0c50850-e2a6-42ef-9f46-9ffaaa637c32

import Definitions.Def_mm_lower
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Theorems.Thm_MarkovMixing_tv_eq_half_l1

/-!
# Distinguishing statistics (LPW Proposition 7.8)
-/

namespace MarkovMixing

noncomputable section
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

private lemma shift_exp (μ : V → ℝ) (hμ : IsDist μ) (f : V → ℝ) (c : ℝ) :
    ∑ x, (f x - c) * μ x = distExp μ f - c := by
  have : ∀ x : V, (f x - c) * μ x = f x * μ x - c * μ x := fun x => by ring
  rw [Finset.sum_congr rfl fun x _ => this x, Finset.sum_sub_distrib, ← Finset.mul_sum,
    hμ.2, mul_one]
  rfl

private lemma shift_var (μ : V → ℝ) (hμ : IsDist μ) (f : V → ℝ) (c : ℝ) :
    ∑ x, (f x - c) ^ 2 * μ x = distVar μ f + (distExp μ f - c) ^ 2 := by
  have hzero : ∑ x, (f x - distExp μ f) * μ x = 0 := by
    rw [shift_exp μ hμ f (distExp μ f)]; ring
  have expand : ∀ x : V, (f x - c) ^ 2 * μ x
      = (f x - distExp μ f) ^ 2 * μ x
        + (2 * (distExp μ f - c)) * ((f x - distExp μ f) * μ x)
        + (distExp μ f - c) ^ 2 * μ x := fun x => by ring
  rw [Finset.sum_congr rfl fun x _ => expand x, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, hzero, ← Finset.mul_sum, hμ.2]
  simp [distVar]

private lemma var_nonneg (μ : V → ℝ) (hμ : IsDist μ) (f : V → ℝ) :
    0 ≤ distVar μ f :=
  Finset.sum_nonneg fun x _ => mul_nonneg (sq_nonneg _) (hμ.1 x)

end

end MarkovMixing

open MarkovMixing

/-- **Proposition 7.8** (LPW). -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (μ ν : V → ℝ) (hμ : IsDist μ) (hν : IsDist ν) (f : V → ℝ)
    (hmean : distExp μ f ≠ distExp ν f)
    (r : ℝ) (hr : 0 ≤ r)
    (h : r * Real.sqrt ((distVar μ f + distVar ν f) / 2) ≤
      |distExp μ f - distExp ν f|) :
    1 - 4 / (4 + r ^ 2) ≤ tvDist μ ν := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (distExp μ f + distExp ν f) / 2 := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = distExp μ f - distExp ν f := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = (distVar μ f + distVar ν f) / 2 := ⟨_, rfl⟩
  have hVμ := var_nonneg μ hμ f
  have hVν := var_nonneg ν hν f
  have hS0 : 0 ≤ S := by rw [hS]; linarith
  have hDne : D ≠ 0 := by rw [hD]; exact sub_ne_zero.mpr hmean
  have hD2pos : 0 < D ^ 2 := by positivity
  -- the shifted statistic
  have hgap : ∑ x, (f x - c) * (μ x - ν x) = D := by
    have h1 : ∑ x, (f x - c) * (μ x - ν x)
        = (∑ x, (f x - c) * μ x) - ∑ x, (f x - c) * ν x := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [h1, shift_exp μ hμ f c, shift_exp ν hν f c, hD]; ring
  -- Cauchy–Schwarz against the signed difference
  have hcs : D ^ 2
      ≤ (∑ x, (f x - c) ^ 2 * |μ x - ν x|) * ∑ x, |μ x - ν x| := by
    rw [← hgap]
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ ?_ ?_ ?_
    · intro x _; exact mul_nonneg (sq_nonneg _) (abs_nonneg _)
    · intro x _; exact abs_nonneg _
    · intro x _
      have h2 : (f x - c) ^ 2 * |μ x - ν x| * |μ x - ν x|
          = ((f x - c) * (μ x - ν x)) ^ 2 := by
        rw [mul_assoc, ← sq, sq_abs]; ring
      exact le_of_eq h2.symm
  -- the ℓ¹ mass is twice the total variation distance
  have habs : ∑ x, |μ x - ν x| = 2 * tvDist μ ν := by
    rw [(tv_eq_half_l1 μ ν hμ hν).1]; ring
  have hsum_nonneg : (0 : ℝ) ≤ ∑ x, |μ x - ν x| :=
    Finset.sum_nonneg fun x _ => abs_nonneg _
  -- bound the weighted second moment by the two second moments
  have hbnd : ∑ x, (f x - c) ^ 2 * |μ x - ν x|
      ≤ (∑ x, (f x - c) ^ 2 * μ x) + ∑ x, (f x - c) ^ 2 * ν x := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun x _ => ?_
    have hle : |μ x - ν x| ≤ μ x + ν x :=
      abs_le.mpr ⟨by linarith [hμ.1 x, hν.1 x], by linarith [hμ.1 x, hν.1 x]⟩
    calc (f x - c) ^ 2 * |μ x - ν x|
        ≤ (f x - c) ^ 2 * (μ x + ν x) :=
          mul_le_mul_of_nonneg_left hle (sq_nonneg _)
      _ = (f x - c) ^ 2 * μ x + (f x - c) ^ 2 * ν x := by ring
  have hSμ : ∑ x, (f x - c) ^ 2 * μ x = distVar μ f + (D / 2) ^ 2 := by
    rw [shift_var μ hμ f c]
    congr 1
    rw [hc, hD]; ring
  have hSν : ∑ x, (f x - c) ^ 2 * ν x = distVar ν f + (D / 2) ^ 2 := by
    rw [shift_var ν hν f c]
    have : distExp ν f - c = -(D / 2) := by rw [hc, hD]; ring
    rw [this]; ring
  -- assemble
  have hmain : D ^ 2 ≤ (4 * S + D ^ 2) * tvDist μ ν := by
    have h3 : (∑ x, (f x - c) ^ 2 * |μ x - ν x|) * (∑ x, |μ x - ν x|)
        ≤ ((distVar μ f + (D / 2) ^ 2) + (distVar ν f + (D / 2) ^ 2))
          * ∑ x, |μ x - ν x| := by
      rw [← hSμ, ← hSν]
      exact mul_le_mul_of_nonneg_right hbnd hsum_nonneg
    have h4 := le_trans hcs h3
    rw [habs] at h4
    have hSS : distVar μ f + distVar ν f = 2 * S := by rw [hS]; ring
    nlinarith [h4, hSS]
  -- the hypothesis, squared
  have hsq : r ^ 2 * S ≤ D ^ 2 := by
    have hnn : 0 ≤ r * Real.sqrt S := mul_nonneg hr (Real.sqrt_nonneg _)
    have h5 : (r * Real.sqrt S) ^ 2 ≤ |D| ^ 2 := by
      refine pow_le_pow_left₀ hnn ?_ 2
      rw [hS, hD] at *
      exact h
    rw [mul_pow, Real.sq_sqrt hS0, sq_abs] at h5
    exact h5
  -- conclude
  have h4pos : (0 : ℝ) < 4 + r ^ 2 := by positivity
  have hden : 0 < 4 * S + D ^ 2 := by linarith
  have hT : D ^ 2 / (4 * S + D ^ 2) ≤ tvDist μ ν := by
    rw [div_le_iff₀ hden]; linarith [hmain]
  have hstep : r ^ 2 / (4 + r ^ 2) ≤ D ^ 2 / (4 * S + D ^ 2) := by
    rw [div_le_div_iff₀ h4pos hden]
    nlinarith [hsq, hS0, sq_nonneg r]
  have hgoal : 1 - 4 / (4 + r ^ 2) = r ^ 2 / (4 + r ^ 2) := by
    field_simp
    ring
  rw [hgoal]
  linarith [hstep, hT]
