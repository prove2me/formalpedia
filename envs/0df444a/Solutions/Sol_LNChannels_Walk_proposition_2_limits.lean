-- Prove2me | solution 1 for LNChannels.Walk.proposition_2_limits
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:20:18.881868+00:00
-- url     : https://prove2.me/submissions/83a35d96-1270-4bfc-937d-476aea7e619b

import Mathlib

set_option autoImplicit false

open Filter Topology

private lemma geomS_eq (n : ℕ) (q : ℝ) :
    ∑ i ∈ Finset.range n, q ^ i =
      (n : ℝ) + (q - 1) * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i, q ^ j := by
  have h : ∀ i ∈ Finset.range n, q ^ i = 1 + (q - 1) * ∑ j ∈ Finset.range i, q ^ j := by
    intro i _
    rw [mul_geom_sum]; ring
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp

private lemma sum_range_real (n : ℕ) : ∑ i ∈ Finset.range n, (i : ℝ) * 2 = (n : ℝ) * ((n : ℝ) - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem solution (l₁ l₂ : ℕ) (hl₁ : 1 ≤ l₁) (hl₂ : 1 ≤ l₂) :
    Tendsto (fun q : ℝ => (q + 1) * (((l₂ : ℝ) * (q ^ l₁ - 1) - l₁) * q ^ l₂ + l₁) /
        ((q - 1) * (q ^ (l₁ + l₂) - 1))) (𝓝[>] 0) (𝓝 (l₁ : ℝ)) ∧
    Tendsto (fun q : ℝ => (q + 1) * (((l₂ : ℝ) * (q ^ l₁ - 1) - l₁) * q ^ l₂ + l₁) /
        ((q - 1) * (q ^ (l₁ + l₂) - 1))) (𝓝[≠] 1) (𝓝 ((l₁ : ℝ) * l₂)) := by
  have hL : l₁ + l₂ ≠ 0 := by omega
  constructor
  · have hc : ContinuousAt (fun q : ℝ => (q + 1) * (((l₂ : ℝ) * (q ^ l₁ - 1) - l₁) * q ^ l₂ + l₁) /
        ((q - 1) * (q ^ (l₁ + l₂) - 1))) 0 := by
      apply ContinuousAt.div (by fun_prop) (by fun_prop)
      simp [zero_pow hL]
    convert hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ))) using 2
    simp [zero_pow hL, zero_pow (by omega : l₂ ≠ 0), zero_pow (by omega : l₁ ≠ 0)]
  · set L := l₁ + l₂ with hLdef
    set A : ℕ → ℝ → ℝ := fun n q => ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i, q ^ j with hA
    set K : ℝ → ℝ := fun q => (l₂ : ℝ) * A L q - (L : ℝ) * A l₂ q with hK
    set S : ℝ → ℝ := fun q => ∑ i ∈ Finset.range L, q ^ i with hS
    set g : ℝ → ℝ := fun q => (q + 1) * K q / S q with hg
    have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero hL
    have hS1 : S 1 = L := by simp [hS]
    have hAc : ∀ n, Continuous (A n) := by
      intro n; simp only [hA]; fun_prop
    have hKc : Continuous K := by
      simp only [hK]; have := hAc L; have := hAc l₂; fun_prop
    have hSc : Continuous S := by simp only [hS]; fun_prop
    have hgc : ContinuousAt g 1 := by
      apply ContinuousAt.div (by have := hKc; fun_prop) hSc.continuousAt
      rw [hS1]; exact hLpos.ne'
    have hA1 : ∀ n, A n 1 * 2 = (n : ℝ) * ((n : ℝ) - 1) := by
      intro n
      simp only [hA, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      have := sum_range_real n
      rw [← Finset.sum_mul] at this
      exact this
    have hg1 : g 1 = (l₁ : ℝ) * l₂ := by
      simp only [hg]
      have h1 := hA1 L
      have h2 := hA1 l₂
      have hK1 : K 1 * 2 = (l₁ : ℝ) * l₂ * L := by
        simp only [hK]
        have hc : (L : ℝ) = l₁ + l₂ := by simp [hLdef]
        have e3 : ((l₂ : ℝ) * A L 1 - (L : ℝ) * A l₂ 1) * 2 =
            (l₂ : ℝ) * (A L 1 * 2) - (L : ℝ) * (A l₂ 1 * 2) := by ring
        rw [e3, h1, h2, hc]; ring
      rw [hS1]
      field_simp
      nlinarith [hK1]
    have key : ∀ q : ℝ, q ≠ 1 → (q + 1) * (((l₂ : ℝ) * (q ^ l₁ - 1) - l₁) * q ^ l₂ + l₁) /
        ((q - 1) * (q ^ (l₁ + l₂) - 1)) = g q := by
      intro q hq
      have hq1 : q - 1 ≠ 0 := sub_ne_zero.mpr hq
      have hSL : q ^ L - 1 = (q - 1) * S q := (mul_geom_sum q L).symm
      have hSl : q ^ l₂ - 1 = (q - 1) * ∑ i ∈ Finset.range l₂, q ^ i := (mul_geom_sum q l₂).symm
      have eL : S q = (L : ℝ) + (q - 1) * A L q := geomS_eq L q
      have el : ∑ i ∈ Finset.range l₂, q ^ i = (l₂ : ℝ) + (q - 1) * A l₂ q := geomS_eq l₂ q
      have hLc : (L : ℝ) = l₁ + l₂ := by simp [hLdef]
      have hnum : ((l₂ : ℝ) * (q ^ l₁ - 1) - l₁) * q ^ l₂ + l₁ = (q - 1) ^ 2 * K q := by
        have : ((l₂ : ℝ) * (q ^ l₁ - 1) - l₁) * q ^ l₂ + l₁ =
            (l₂ : ℝ) * (q ^ L - 1) - (L : ℝ) * (q ^ l₂ - 1) := by
          rw [hLdef, pow_add]; push_cast; ring
        rw [this, hSL, hSl, eL, el]
        simp only [hK]
        rw [hLc]; ring
      have hden : (q - 1) * (q ^ (l₁ + l₂) - 1) = (q - 1) ^ 2 * S q := by
        rw [← hLdef, hSL]; ring
      rw [hnum, hden]
      simp only [hg]
      rw [show (q + 1) * ((q - 1) ^ 2 * K q) = (q - 1) ^ 2 * ((q + 1) * K q) by ring]
      exact mul_div_mul_left _ _ (pow_ne_zero 2 hq1)
    have h := hgc.tendsto
    rw [hg1] at h
    refine (h.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact (key q hq).symm
