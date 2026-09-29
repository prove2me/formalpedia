-- Prove2me | solution 1 for MarkovMixing.tv_sup_functions
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-08-22T03:56:55.176286+00:00
-- url     : https://prove2.me/submissions/6ef9c9bd-1a0b-4cc7-b507-7cc5b98f7226

import Theorems.Thm_MarkovMixing_tv_eq_half_l1
import Mathlib.Tactic.Linarith

open scoped BigOperators
open MarkovMixing

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (μ ν : V → ℝ) (hμ : IsDist μ) (hν : IsDist ν) :
    tvDist μ ν =
      2⁻¹ * ⨆ f : {f : V → ℝ // ∀ x, |f x| ≤ 1},
        |∑ x, (f : V → ℝ) x * μ x - ∑ x, (f : V → ℝ) x * ν x| := by
  classical
  haveI : Nonempty {f : V → ℝ // ∀ x, |f x| ≤ 1} := ⟨⟨fun _ => 0, fun x => by simp⟩⟩
  have hl1 : ∑ x, |μ x - ν x| = 2 * tvDist μ ν := by
    rw [(MarkovMixing.tv_eq_half_l1 μ ν hμ hν).1]
    ring
  set F : {f : V → ℝ // ∀ x, |f x| ≤ 1} → ℝ :=
    fun f => |∑ x, (f : V → ℝ) x * μ x - ∑ x, (f : V → ℝ) x * ν x| with hF
  -- every test function is dominated by the ℓ¹ distance
  have hFle : ∀ f : {f : V → ℝ // ∀ x, |f x| ≤ 1}, F f ≤ 2 * tvDist μ ν := by
    intro f
    have hrw : ∑ x, (f : V → ℝ) x * μ x - ∑ x, (f : V → ℝ) x * ν x
        = ∑ x, (f : V → ℝ) x * (μ x - ν x) := by
      rw [Finset.sum_congr rfl fun x _ => mul_sub ((f : V → ℝ) x) (μ x) (ν x),
        Finset.sum_sub_distrib]
    rw [hF]
    simp only
    rw [hrw, ← hl1]
    calc |∑ x, (f : V → ℝ) x * (μ x - ν x)|
        ≤ ∑ x, |(f : V → ℝ) x * (μ x - ν x)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x, |μ x - ν x| := by
          refine Finset.sum_le_sum fun x _ => ?_
          rw [abs_mul]
          calc |(f : V → ℝ) x| * |μ x - ν x| ≤ 1 * |μ x - ν x| :=
                mul_le_mul_of_nonneg_right (f.2 x) (abs_nonneg _)
            _ = |μ x - ν x| := one_mul _
  have hbdd : BddAbove (Set.range F) := ⟨2 * tvDist μ ν, by
    rintro a ⟨f, rfl⟩
    exact hFle f⟩
  -- the sign function attains the bound
  set g : V → ℝ := fun x => if ν x ≤ μ x then (1:ℝ) else -1 with hg
  have hgle : ∀ x, |g x| ≤ 1 := by
    intro x
    by_cases h : ν x ≤ μ x <;> simp [hg, h]
  have hgval : F ⟨g, hgle⟩ = 2 * tvDist μ ν := by
    have hrw : ∑ x, g x * μ x - ∑ x, g x * ν x = ∑ x, g x * (μ x - ν x) := by
      rw [Finset.sum_congr rfl fun x _ => mul_sub (g x) (μ x) (ν x), Finset.sum_sub_distrib]
    have hpt : ∀ x : V, g x * (μ x - ν x) = |μ x - ν x| := by
      intro x
      by_cases h : ν x ≤ μ x
      · rw [hg]
        simp only [if_pos h, one_mul]
        rw [abs_of_nonneg (by linarith)]
      · rw [hg]
        simp only [if_neg h]
        push_neg at h
        rw [abs_of_nonpos (by linarith)]
        ring
    rw [hF]
    simp only
    rw [hrw, Finset.sum_congr rfl fun x _ => hpt x, hl1,
      abs_of_nonneg (by linarith [(MarkovMixing.tv_eq_half_l1 μ ν hμ hν).1,
        Finset.sum_nonneg (fun x (_ : x ∈ Finset.univ) => abs_nonneg (μ x - ν x)), hl1])]
  have hsup : (⨆ f : {f : V → ℝ // ∀ x, |f x| ≤ 1},
      |∑ x, (f : V → ℝ) x * μ x - ∑ x, (f : V → ℝ) x * ν x|) = 2 * tvDist μ ν := by
    refine le_antisymm (ciSup_le hFle) ?_
    rw [← hgval]
    exact le_ciSup hbdd ⟨g, hgle⟩
  rw [hsup]
  ring
