-- Prove2me | solution 1 for MarkovMixing.distinguishing_statistic_of_pos_variance
-- status  : ACCEPTED   (prove)
-- author  : @chenmin
-- created : 2026-08-22T16:34:10.959611+00:00
-- url     : https://prove2.me/submissions/d15cef00-f4b7-4f49-ba1a-80510ab8f35b

import Definitions.Def_mm_lower
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

set_option maxHeartbeats 1000000

open scoped BigOperators
open MarkovMixing

namespace DistStat

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma le_tvDist (μ ν : V → ℝ) (A : Finset V) :
    |∑ x ∈ A, μ x - ∑ x ∈ A, ν x| ≤ tvDist μ ν := by
  have hb : BddAbove (Set.range fun B : Finset V => |∑ x ∈ B, μ x - ∑ x ∈ B, ν x|) :=
    Set.Finite.bddAbove (Set.finite_range _)
  exact le_ciSup hb A

lemma l1_le_two_tvDist (μ ν : V → ℝ) : ∑ y, |μ y - ν y| ≤ 2 * tvDist μ ν := by
  classical
  set A : Finset V := Finset.univ.filter fun y => ν y ≤ μ y with hA
  have hsplit : ∑ y, |μ y - ν y|
      = (∑ y ∈ A, (μ y - ν y)) + ∑ y ∈ Aᶜ, (ν y - μ y) := by
    rw [← Finset.sum_add_sum_compl A (fun y => |μ y - ν y|)]
    congr 1
    · refine Finset.sum_congr rfl fun y hy => ?_
      rw [hA, Finset.mem_filter] at hy
      exact abs_of_nonneg (by linarith [hy.2])
    · refine Finset.sum_congr rfl fun y hy => ?_
      rw [Finset.mem_compl, hA, Finset.mem_filter] at hy
      have hlt : ¬ (ν y ≤ μ y) := fun hle => hy ⟨Finset.mem_univ y, hle⟩
      rw [abs_of_nonpos (by linarith [not_le.mp hlt])]
      ring
  have h1 : ∑ y ∈ A, (μ y - ν y) ≤ tvDist μ ν := by
    calc ∑ y ∈ A, (μ y - ν y) = ∑ y ∈ A, μ y - ∑ y ∈ A, ν y := Finset.sum_sub_distrib _ _
      _ ≤ |∑ y ∈ A, μ y - ∑ y ∈ A, ν y| := le_abs_self _
      _ ≤ tvDist μ ν := le_tvDist μ ν A
  have h2 : ∑ y ∈ Aᶜ, (ν y - μ y) ≤ tvDist μ ν := by
    calc ∑ y ∈ Aᶜ, (ν y - μ y) = -(∑ y ∈ Aᶜ, μ y - ∑ y ∈ Aᶜ, ν y) := by
          rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun y _ => by ring
      _ ≤ |∑ y ∈ Aᶜ, μ y - ∑ y ∈ Aᶜ, ν y| := neg_le_abs _
      _ ≤ tvDist μ ν := le_tvDist μ ν Aᶜ
  rw [hsplit]
  linarith

end DistStat

open DistStat

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (μ ν : V → ℝ) (hμ : MarkovMixing.IsDist μ) (hν : MarkovMixing.IsDist ν) (f : V → ℝ)
    (hvar : 0 < MarkovMixing.distVar μ f + MarkovMixing.distVar ν f)
    (r : ℝ) (hr : 0 ≤ r)
    (h : r * Real.sqrt ((MarkovMixing.distVar μ f + MarkovMixing.distVar ν f) / 2) ≤
      |MarkovMixing.distExp μ f - MarkovMixing.distExp ν f|) :
    1 - 4 / (4 + r ^ 2) ≤ MarkovMixing.tvDist μ ν := by
  classical
  set m : ℝ := (distExp μ f + distExp ν f) / 2 with hm_def
  set M : ℝ := (distExp μ f - distExp ν f) / 2 with hM_def
  set σ2 : ℝ := (distVar μ f + distVar ν f) / 2 with hσ2_def
  have hσ2pos : 0 < σ2 := by rw [hσ2_def]; linarith
  set g : V → ℝ := fun x => f x - m with hg_def
  have keyl : ∀ ρ : V → ℝ, (∑ x, ρ x = 1) → ∑ x, g x * ρ x = distExp ρ f - m := by
    intro ρ hρ
    have e : ∀ x : V, g x * ρ x = f x * ρ x - m * ρ x := fun x => by rw [hg_def]; ring
    rw [Finset.sum_congr rfl (fun x _ => e x), Finset.sum_sub_distrib, ← Finset.mul_sum, hρ,
      mul_one]
    rfl
  have keyq : ∀ ρ : V → ℝ, (∑ x, ρ x = 1) →
      ∑ x, g x ^ 2 * ρ x = distVar ρ f + (distExp ρ f - m) ^ 2 := by
    intro ρ hρ
    have e : ∀ x : V, g x ^ 2 * ρ x
        = (f x - distExp ρ f) ^ 2 * ρ x
          + 2 * (distExp ρ f - m) * ((f x - distExp ρ f) * ρ x)
          + (distExp ρ f - m) ^ 2 * ρ x := fun x => by rw [hg_def]; ring
    have e2 : ∑ x, (f x - distExp ρ f) * ρ x = 0 := by
      have e3 : ∀ x : V, (f x - distExp ρ f) * ρ x = f x * ρ x - distExp ρ f * ρ x :=
        fun x => by ring
      rw [Finset.sum_congr rfl (fun x _ => e3 x), Finset.sum_sub_distrib, ← Finset.mul_sum, hρ,
        mul_one]
      show distExp ρ f - distExp ρ f = 0
      ring
    rw [Finset.sum_congr rfl (fun x _ => e x), Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, e2, hρ, mul_zero, mul_one, add_zero]
    rfl
  have hEμ : distExp μ f - m = M := by rw [hm_def, hM_def]; ring
  have hEν : distExp ν f - m = -M := by rw [hm_def, hM_def]; ring
  have hLsum : ∑ x, g x * (μ x - ν x) = 2 * M := by
    have e : ∀ x : V, g x * (μ x - ν x) = g x * μ x - g x * ν x := fun x => by ring
    rw [Finset.sum_congr rfl (fun x _ => e x), Finset.sum_sub_distrib, keyl μ hμ.2, keyl ν hν.2,
      hEμ, hEν]
    ring
  have hFsum : ∑ x, g x ^ 2 * ((μ x + ν x) / 2) = σ2 + M ^ 2 := by
    have e : ∀ x : V, g x ^ 2 * ((μ x + ν x) / 2)
        = (g x ^ 2 * μ x) / 2 + (g x ^ 2 * ν x) / 2 := fun x => by ring
    rw [Finset.sum_congr rfl (fun x _ => e x), Finset.sum_add_distrib, ← Finset.sum_div,
      ← Finset.sum_div, keyq μ hμ.2, keyq ν hν.2, hEμ, hEν, hσ2_def]
    ring
  have hGsum : ∑ x, 2 * |μ x - ν x| ≤ 4 * tvDist μ ν := by
    rw [← Finset.mul_sum]
    linarith [l1_le_two_tvDist μ ν]
  have hCS := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset V)
    (r := fun x => g x * (μ x - ν x))
    (f := fun x => g x ^ 2 * ((μ x + ν x) / 2))
    (g := fun x => 2 * |μ x - ν x|)
    (fun x _ => mul_nonneg (sq_nonneg _) (by linarith [hμ.1 x, hν.1 x]))
    (fun x _ => by positivity)
    (fun x _ => by
      have hab : |μ x - ν x| ≤ μ x + ν x := by
        rw [abs_le]
        constructor <;> linarith [hμ.1 x, hν.1 x]
      calc (g x * (μ x - ν x)) ^ 2 = g x ^ 2 * (|μ x - ν x| * |μ x - ν x|) := by
            rw [abs_mul_abs_self]; ring
        _ ≤ g x ^ 2 * ((μ x + ν x) * |μ x - ν x|) := by
            refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
            exact mul_le_mul_of_nonneg_right hab (abs_nonneg _)
        _ = g x ^ 2 * ((μ x + ν x) / 2) * (2 * |μ x - ν x|) := by ring)
  rw [hLsum, hFsum] at hCS
  have hMS : 0 < M ^ 2 + σ2 := by positivity
  have hMsq : M ^ 2 ≤ (σ2 + M ^ 2) * tvDist μ ν := by
    have h1 : (2 * M) ^ 2 ≤ (σ2 + M ^ 2) * (4 * tvDist μ ν) := by
      refine hCS.trans ?_
      exact mul_le_mul_of_nonneg_left hGsum (by linarith)
    nlinarith
  have habs : |distExp μ f - distExp ν f| = 2 * |M| := by
    rw [hM_def, abs_div]
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    field_simp
  have hsq : r ^ 2 * σ2 ≤ 4 * M ^ 2 := by
    rw [habs] at h
    have h2 : (r * Real.sqrt σ2) ^ 2 ≤ (2 * |M|) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h 2
    rw [mul_pow, Real.sq_sqrt hσ2pos.le, mul_pow, sq_abs] at h2
    linarith
  have hd : (0:ℝ) < 4 + r ^ 2 := by positivity
  have hfin : (1 - 4 / (4 + r ^ 2)) * (M ^ 2 + σ2) ≤ M ^ 2 := by
    have hrw : (1 - 4 / (4 + r ^ 2)) = r ^ 2 / (4 + r ^ 2) := by field_simp; ring
    rw [hrw, div_mul_eq_mul_div, div_le_iff₀ hd]
    nlinarith
  have hstep : (1 - 4 / (4 + r ^ 2)) * (M ^ 2 + σ2) ≤ tvDist μ ν * (M ^ 2 + σ2) := by
    nlinarith
  exact le_of_mul_le_mul_right hstep hMS
