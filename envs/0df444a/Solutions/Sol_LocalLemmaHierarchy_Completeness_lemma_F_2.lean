-- Prove2me | solution 1 for LocalLemmaHierarchy.Completeness.lemma_F_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:21:51.500533+00:00
-- url     : https://prove2.me/submissions/ab0a66d0-fb5c-4b86-b95e-10530f9a4804

import Mathlib
import Definitions.Def_LocalLemmaHierarchy_Completeness_Weights

section
set_option autoImplicit false

namespace LocalLemmaHierarchy.Completeness.Dev.F2

open Finset

theorem prod_rpow_sqrt {ι : Type} [Fintype ι] (p t : ι → ℝ) (ht : ∀ i, 0 ≤ t i) :
    ∏ i, t i ^ p i = (∏ i, Real.sqrt (t i) ^ p i) ^ 2 := by
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  show _ = (Real.sqrt (t i) ^ p i) ^ (2:ℕ)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Real.sqrt_nonneg _), mul_comm, Real.rpow_mul
    (Real.sqrt_nonneg _), Real.rpow_natCast, Real.sq_sqrt (ht i)]

theorem gm_le {ι : Type} [Fintype ι] (p μ t : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hμ : ∀ i, 0 ≤ μ i) (hs : ∀ i, μ i = 0 → p i = 0) (ht : ∀ i, 0 ≤ t i) :
    ∏ i, t i ^ p i ≤ (∑ i ∈ univ.filter (fun i => 0 < μ i), p i ^ 2 / μ i) *
      (∑ i ∈ univ.filter (fun i => 0 < μ i), μ i * t i) := by
  rw [prod_rpow_sqrt p t ht]
  have h2 : ∏ i, Real.sqrt (t i) ^ p i ≤ ∑ i, p i * Real.sqrt (t i) :=
    Real.geom_mean_le_arith_mean_weighted _ _ _ (fun i _ => hp i) hp1
      (fun i _ => Real.sqrt_nonneg _)
  have h0 : 0 ≤ ∏ i, Real.sqrt (t i) ^ p i :=
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have h3 : ∑ i, p i * Real.sqrt (t i) =
      ∑ i ∈ univ.filter (fun i => 0 < μ i), p i * Real.sqrt (t i) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    have : μ i = 0 := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
      exact le_antisymm hi (hμ i)
    simp [hs i this]
  calc (∏ i, Real.sqrt (t i) ^ p i) ^ 2 ≤ (∑ i, p i * Real.sqrt (t i)) ^ 2 :=
        pow_le_pow_left₀ h0 h2 2
    _ = (∑ i ∈ univ.filter (fun i => 0 < μ i),
          (p i / Real.sqrt (μ i)) * (Real.sqrt (μ i) * Real.sqrt (t i))) ^ 2 := by
        rw [h3]
        congr 1
        refine Finset.sum_congr rfl fun i hi => ?_
        have : 0 < μ i := (Finset.mem_filter.mp hi).2
        have : Real.sqrt (μ i) ≠ 0 := (Real.sqrt_pos.mpr this).ne'
        field_simp
    _ ≤ (∑ i ∈ univ.filter (fun i => 0 < μ i), (p i / Real.sqrt (μ i)) ^ 2) *
          (∑ i ∈ univ.filter (fun i => 0 < μ i), (Real.sqrt (μ i) * Real.sqrt (t i)) ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = _ := by
        congr 1
        · refine Finset.sum_congr rfl fun i hi => ?_
          have h : 0 < μ i := (Finset.mem_filter.mp hi).2
          rw [div_pow, Real.sq_sqrt h.le]
        · refine Finset.sum_congr rfl fun i hi => ?_
          rw [mul_pow, Real.sq_sqrt (hμ i), Real.sq_sqrt (ht i)]

end LocalLemmaHierarchy.Completeness.Dev.F2

namespace LocalLemmaHierarchy.Completeness

open Dev.F2 Finset

theorem chk_lemma_F_2 {ι : Type} [Fintype ι] (α β : ι → ℝ) (hα : ∀ i, 0 ≤ α i)
    (hα1 : ∑ i, α i = 1) (hβ : ∀ i, 0 ≤ β i) (hβ1 : ∑ i, β i = 1) (z : ι → ℝ)
    (hz : ∀ i, 0 ≤ z i ∧ z i ≤ 1) :
    geomMean α z + geomMean β (fun i => 1 - z i) ≤
        1 + (1 / 2) * ∑ i ∈ Finset.univ.filter (fun i => 0 < α i + β i),
          (α i - β i) ^ 2 / (α i + β i) ∧
    1 + (1 / 2) * ∑ i ∈ Finset.univ.filter (fun i => 0 < α i + β i),
          (α i - β i) ^ 2 / (α i + β i) ≤
        1 + ∑ i, (Real.sqrt (α i) - Real.sqrt (β i)) ^ 2 := by
  constructor
  · obtain ⟨μ, hμdef⟩ : ∃ μ : ι → ℝ, μ = fun i => (α i + β i) / 2 := ⟨_, rfl⟩
    have hμ : ∀ i, 0 ≤ μ i := fun i => by have := hα i; have := hβ i; simp only [hμdef]; linarith
    have hfilt : univ.filter (fun i => 0 < μ i) = univ.filter (fun i => 0 < α i + β i) := by
      ext i; simp only [hμdef, mem_filter, mem_univ, true_and]; constructor <;> intro h <;> linarith
    have hsα : ∀ i, μ i = 0 → α i = 0 := fun i h => by
      have := hα i; have := hβ i; simp only [hμdef] at h; linarith
    have hsβ : ∀ i, μ i = 0 → β i = 0 := fun i h => by
      have := hα i; have := hβ i; simp only [hμdef] at h; linarith
    have supp : ∀ f : ι → ℝ, (∀ i, μ i = 0 → f i = 0) →
        ∑ i ∈ univ.filter (fun i => 0 < μ i), f i = ∑ i, f i := by
      intro f hf
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i _ hi
      apply hf
      simp only [mem_filter, mem_univ, true_and, not_lt] at hi
      exact le_antisymm hi (hμ i)
    set D := ∑ i ∈ univ.filter (fun i => 0 < α i + β i), (α i - β i) ^ 2 / (α i + β i) with hD
    have hKα : ∑ i ∈ univ.filter (fun i => 0 < μ i), α i ^ 2 / μ i = 1 + (1 / 2) * D := by
      have : ∀ i ∈ univ.filter (fun i => 0 < μ i), α i ^ 2 / μ i =
          μ i + (α i - β i) + (1 / 2) * ((α i - β i) ^ 2 / (α i + β i)) := by
        intro i hi
        have h : 0 < α i + β i := by
          have := (mem_filter.mp hi).2; simp only [hμdef] at this; linarith
        simp only [hμdef]; field_simp; ring
      have e1 : ∑ i ∈ univ.filter (fun i => 0 < μ i), μ i = 1 := by
        rw [supp μ (fun i h => h)]
        simp only [hμdef, ← Finset.sum_div, Finset.sum_add_distrib, hα1, hβ1]; norm_num
      have e2 : ∑ i ∈ univ.filter (fun i => 0 < μ i), (α i - β i) = 0 := by
        rw [supp _ (fun i h => by rw [hsα i h, hsβ i h]; simp), Finset.sum_sub_distrib, hα1, hβ1]
        simp
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        e1, e2, hfilt]; ring
    have hKβ : ∑ i ∈ univ.filter (fun i => 0 < μ i), β i ^ 2 / μ i = 1 + (1 / 2) * D := by
      have : ∀ i ∈ univ.filter (fun i => 0 < μ i), β i ^ 2 / μ i =
          μ i + (β i - α i) + (1 / 2) * ((α i - β i) ^ 2 / (α i + β i)) := by
        intro i hi
        have h : 0 < α i + β i := by
          have := (mem_filter.mp hi).2; simp only [hμdef] at this; linarith
        simp only [hμdef]; field_simp; ring
      have e1 : ∑ i ∈ univ.filter (fun i => 0 < μ i), μ i = 1 := by
        rw [supp μ (fun i h => h)]
        simp only [hμdef, ← Finset.sum_div, Finset.sum_add_distrib, hα1, hβ1]; norm_num
      have e2 : ∑ i ∈ univ.filter (fun i => 0 < μ i), (β i - α i) = 0 := by
        rw [supp _ (fun i h => by rw [hsα i h, hsβ i h]; simp), Finset.sum_sub_distrib, hα1, hβ1]
        simp
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        e1, e2, hfilt]; ring
    have g1 := gm_le α μ z hα hα1 hμ hsα (fun i => (hz i).1)
    have g2 := gm_le β μ (fun i => 1 - z i) hβ hβ1 hμ hsβ (fun i => by linarith [(hz i).2])
    rw [hKα] at g1
    rw [hKβ] at g2
    unfold geomMean
    have hsum : ∑ i ∈ univ.filter (fun i => 0 < μ i), μ i * z i +
        ∑ i ∈ univ.filter (fun i => 0 < μ i), μ i * (1 - z i) = 1 := by
      rw [← Finset.sum_add_distrib]
      have : ∀ i ∈ univ.filter (fun i => 0 < μ i), μ i * z i + μ i * (1 - z i) = μ i := by
        intro i _; ring
      rw [Finset.sum_congr rfl this, supp μ (fun i h => h)]
      simp only [hμdef, ← Finset.sum_div, Finset.sum_add_distrib, hα1, hβ1]; norm_num
    calc _ ≤ _ := add_le_add g1 g2
      _ = (1 + 1 / 2 * D) * (∑ i ∈ univ.filter (fun i => 0 < μ i), μ i * z i +
        ∑ i ∈ univ.filter (fun i => 0 < μ i), μ i * (1 - z i)) := by ring
      _ = _ := by rw [hsum, mul_one]
  · have : ∀ i ∈ univ.filter (fun i => 0 < α i + β i),
        (1 / 2) * ((α i - β i) ^ 2 / (α i + β i)) ≤ (Real.sqrt (α i) - Real.sqrt (β i)) ^ 2 := by
      intro i hi
      have h : 0 < α i + β i := (mem_filter.mp hi).2
      have ha := Real.sq_sqrt (hα i)
      have hb := Real.sq_sqrt (hβ i)
      have sa := Real.sqrt_nonneg (α i)
      have sb := Real.sqrt_nonneg (β i)
      have e : (α i - β i) ^ 2 = (Real.sqrt (α i) - Real.sqrt (β i)) ^ 2 *
          (Real.sqrt (α i) + Real.sqrt (β i)) ^ 2 := by
        rw [← mul_pow]; rw [← ha, ← hb]; ring_nf; simp [Real.sq_sqrt (hα i), Real.sq_sqrt (hβ i)]
      rw [e, ← mul_div_assoc, div_le_iff₀ h]
      have hs : (Real.sqrt (α i) + Real.sqrt (β i)) ^ 2 ≤ 2 * (α i + β i) := by
        nlinarith [sq_nonneg (Real.sqrt (α i) - Real.sqrt (β i))]
      have := mul_le_mul_of_nonneg_left hs (sq_nonneg (Real.sqrt (α i) - Real.sqrt (β i)))
      nlinarith
    have hle : (1 / 2) * ∑ i ∈ univ.filter (fun i => 0 < α i + β i),
          (α i - β i) ^ 2 / (α i + β i) ≤ ∑ i, (Real.sqrt (α i) - Real.sqrt (β i)) ^ 2 := by
      rw [Finset.mul_sum]
      calc _ ≤ ∑ i ∈ univ.filter (fun i => 0 < α i + β i),
            (Real.sqrt (α i) - Real.sqrt (β i)) ^ 2 := Finset.sum_le_sum this
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun i _ _ => sq_nonneg _)
    linarith

end LocalLemmaHierarchy.Completeness
end

theorem solution : type_of% @LocalLemmaHierarchy.Completeness.chk_lemma_F_2 := @LocalLemmaHierarchy.Completeness.chk_lemma_F_2
