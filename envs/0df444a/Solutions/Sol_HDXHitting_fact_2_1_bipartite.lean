-- Prove2me | solution 1 for HDXHitting.fact_2_1_bipartite
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:07:52.681886+00:00
-- url     : https://prove2.me/submissions/80852c2d-8d19-4f34-970c-93252ee83d4f

import Mathlib
import Definitions.Def_HDXHitting_BipSingLE

section
set_option autoImplicit false
namespace HDXHitting.Dev.Bip
/-- variance bound: `∑ L f² ≤ ∑ L f = μ` for `0 ≤ f ≤ 1`, `L ≥ 0`. -/
lemma sq_le {U : Type*} [Fintype U] (L f : U → ℝ) (hL : ∀ u, 0 ≤ L u)
    (hf : ∀ u, 0 ≤ f u ∧ f u ≤ 1) : ∑ u, L u * f u ^ 2 ≤ ∑ u, L u * f u :=
  Finset.sum_le_sum (fun u _ => by
    have := hf u
    exact mul_le_mul_of_nonneg_left (by nlinarith [this.1, this.2]) (hL u))
end HDXHitting.Dev.Bip
namespace HDXHitting
open HDXHitting.Dev.Bip in
theorem chk_fact_2_1_bipartite {U W : Type*} [Fintype U] [Fintype W] (B : U → W → ℝ)
    (hB0 : ∀ u w, 0 ≤ B u w) (hB1 : ∑ u, ∑ w, B u w = 1) (lam : ℝ) (hlam : 0 ≤ lam)
    (hB : BipSingLE B lam) (f : U → ℝ) (g : W → ℝ) (hf : ∀ u, 0 ≤ f u ∧ f u ≤ 1)
    (hg : ∀ w, 0 ≤ g w ∧ g w ≤ 1) (μ ν : ℝ) (hμ : μ = ∑ u, (∑ w, B u w) * f u)
    (hν : ν = ∑ w, (∑ u, B u w) * g w) :
    |∑ u, ∑ w, B u w * f u * g w - μ * ν| ≤ lam * Real.sqrt (μ * (1 - μ) * ν * (1 - ν)) ∧
      lam * Real.sqrt (μ * (1 - μ) * ν * (1 - ν)) ≤ lam * Real.sqrt (μ * ν) := by
  classical
  set L : U → ℝ := fun u => ∑ w, B u w with hLd
  set R : W → ℝ := fun w => ∑ u, B u w with hRd
  have hL0 : ∀ u, 0 ≤ L u := fun u => Finset.sum_nonneg (fun w _ => hB0 u w)
  have hR0 : ∀ w, 0 ≤ R w := fun w => Finset.sum_nonneg (fun u _ => hB0 u w)
  have hL1 : ∑ u, L u = 1 := hB1
  have hR1 : ∑ w, R w = 1 := by
    simp only [hRd]; rw [Finset.sum_comm]; exact hB1
  have hLf : ∑ u, ∑ w, B u w * f u = μ := by
    rw [hμ]; exact Finset.sum_congr rfl (fun u _ => by rw [Finset.sum_mul])
  have hRg : ∑ u, ∑ w, B u w * g w = ν := by
    rw [Finset.sum_comm, hν]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [Finset.sum_mul]
  have hB1' : ∑ u, ∑ w, B u w = 1 := hL1
  have hμ0 : 0 ≤ μ := by rw [hμ]; exact Finset.sum_nonneg (fun u _ => mul_nonneg (hL0 u) (hf u).1)
  have hν0 : 0 ≤ ν := by rw [hν]; exact Finset.sum_nonneg (fun w _ => mul_nonneg (hR0 w) (hg w).1)
  have hμ1 : μ ≤ 1 := by
    rw [hμ, ← hL1]; exact Finset.sum_le_sum (fun u _ => by
      have := hf u; nlinarith [hL0 u])
  have hν1 : ν ≤ 1 := by
    rw [hν, ← hR1]; exact Finset.sum_le_sum (fun w _ => by
      have := hg w; nlinarith [hR0 w])
  have hg0 : ∑ u, L u * (f u - μ) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hL1]
    rw [← hμ]; ring
  have hk0 : ∑ w, R w * (g w - ν) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hR1]
    rw [← hν]; ring
  have key := hB (fun u => f u - μ) (fun w => g w - ν) hg0 hk0
  have e1 : ∑ u, ∑ w, B u w * (f u - μ) * (g w - ν)
      = ∑ u, ∑ w, B u w * f u * g w - μ * ν := by
    have : ∀ u w, B u w * (f u - μ) * (g w - ν)
        = B u w * f u * g w - ν * (B u w * f u) - μ * (B u w * g w) + μ * ν * B u w := by
      intros; ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hLf, hRg, hB1']
    ring
  have e2 : ∑ u, L u * (f u - μ) ^ 2 = ∑ u, L u * f u ^ 2 - μ ^ 2 := by
    have : ∀ u, L u * (f u - μ) ^ 2
        = L u * f u ^ 2 - 2 * μ * (L u * f u) + μ ^ 2 * L u := fun u => by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hL1]
    rw [← hμ]; ring
  have e3 : ∑ w, R w * (g w - ν) ^ 2 = ∑ w, R w * g w ^ 2 - ν ^ 2 := by
    have : ∀ w, R w * (g w - ν) ^ 2
        = R w * g w ^ 2 - 2 * ν * (R w * g w) + ν ^ 2 * R w := fun w => by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hR1]
    rw [← hν]; ring
  have s1 := sq_le L f hL0 hf
  have s2 := sq_le R g hR0 hg
  rw [← hμ] at s1
  rw [← hν] at s2
  have v1 : ∑ u, L u * (f u - μ) ^ 2 ≤ μ * (1 - μ) := by rw [e2]; nlinarith
  have v2 : ∑ w, R w * (g w - ν) ^ 2 ≤ ν * (1 - ν) := by rw [e3]; nlinarith
  have v1n : 0 ≤ ∑ u, L u * (f u - μ) ^ 2 :=
    Finset.sum_nonneg (fun u _ => mul_nonneg (hL0 u) (sq_nonneg _))
  have v2n : 0 ≤ ∑ w, R w * (g w - ν) ^ 2 :=
    Finset.sum_nonneg (fun w _ => mul_nonneg (hR0 w) (sq_nonneg _))
  rw [e1] at key
  have hQ : 0 ≤ μ * (1 - μ) * ν * (1 - ν) := by
    have : 0 ≤ μ * (1 - μ) := mul_nonneg hμ0 (by linarith)
    have : 0 ≤ ν * (1 - ν) := mul_nonneg hν0 (by linarith)
    nlinarith [mul_nonneg ‹0 ≤ μ * (1 - μ)› ‹0 ≤ ν * (1 - ν)›]
  have hsq : (∑ u, ∑ w, B u w * f u * g w - μ * ν) ^ 2 ≤ (lam * Real.sqrt (μ * (1 - μ) * ν * (1 - ν))) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hQ]
    refine key.trans ?_
    have h12 : (∑ u, L u * (f u - μ) ^ 2) * (∑ w, R w * (g w - ν) ^ 2) ≤ μ * (1 - μ) * (ν * (1 - ν)) :=
      mul_le_mul v1 v2 v2n (by nlinarith)
    have := mul_le_mul_of_nonneg_left h12 (sq_nonneg lam)
    nlinarith [this]
  refine ⟨abs_le_of_sq_le_sq hsq (mul_nonneg hlam (Real.sqrt_nonneg _)), ?_⟩
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hlam
  have : (1 - μ) * (1 - ν) ≤ 1 := by nlinarith
  nlinarith [mul_nonneg hμ0 hν0, mul_le_mul_of_nonneg_left this (mul_nonneg hμ0 hν0)]
end HDXHitting
end

theorem solution : type_of% @HDXHitting.chk_fact_2_1_bipartite := @HDXHitting.chk_fact_2_1_bipartite
