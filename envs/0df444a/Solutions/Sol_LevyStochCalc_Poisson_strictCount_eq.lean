-- Prove2me | solution 1 for LevyStochCalc.Poisson.strictCount_eq
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T14:23:53.64305+00:00
-- url     : https://prove2.me/submissions/414d5f01-1cdb-4283-9fab-9e280303f0b1

import Definitions.Def_LevyStochCalc_Poisson_StrictCount_F000

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
open LevyStochCalc.Poisson

theorem solution {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (N : PoissonRandomMeasure P ν)
    {C : Set (ℝ × E)} {A : Set E} {T s : ℝ} (hs : 0 < s) (hsT : s ≤ T)
    {e : E} (he : e ∈ A) (ω : Ω) :
    strictCount N C A T ω s e = N.N ω (C ∩ Set.Ioo (0 : ℝ) s ×ˢ Set.univ) := by
  classical
  -- the dyadic index of the slab containing `s`
  let k : ℕ → ℕ := fun n => ⌈s * 2 ^ n⌉₊ - 1
  have hpos : ∀ n : ℕ, 0 < s * 2 ^ n := fun n => by positivity
  have hceil1 : ∀ n, 1 ≤ ⌈s * 2 ^ n⌉₊ := fun n => Nat.one_le_iff_ne_zero.mpr
    (by rw [Ne, Nat.ceil_eq_zero, not_le]; exact hpos n)
  have hk1 : ∀ n, k n + 1 = ⌈s * 2 ^ n⌉₊ := fun n => Nat.sub_add_cancel (hceil1 n)
  have hklt : ∀ n, (k n : ℝ) < s * 2 ^ n := by
    intro n
    have h := Nat.ceil_lt_add_one (hpos n).le
    have : ((k n + 1 : ℕ) : ℝ) < s * 2 ^ n + 1 := by rw [hk1]; exact h
    push_cast at this; linarith
  have hkge : ∀ n, s * 2 ^ n ≤ (k n : ℝ) + 1 := by
    intro n
    have h := Nat.le_ceil (s * 2 ^ n)
    rw [← hk1] at h; push_cast at h; exact h
  -- membership in a slab picks out `k n`
  have hmem : ∀ (n : ℕ) (i : ℕ), (s, e) ∈ Set.Ioc ((i : ℝ) / 2 ^ n) (((i : ℝ) + 1) / 2 ^ n) ×ˢ A ↔ i = k n := by
    intro n i
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    simp only [Set.mem_prod, Set.mem_Ioc, he, and_true]
    rw [div_lt_iff₀ h2, le_div_iff₀ h2]
    constructor
    · rintro ⟨h1, h2'⟩
      have : (⌈s * 2 ^ n⌉₊ : ℕ) = i + 1 := by
        rw [Nat.ceil_eq_iff (Nat.succ_ne_zero i)]
        push_cast; simpa using ⟨h1, h2'⟩
      have := hk1 n; omega
    · rintro rfl; exact ⟨hklt n, hkge n⟩
  have hkT : ∀ n, k n < ⌈T * 2 ^ n⌉₊ := by
    intro n
    have : ⌈s * 2 ^ n⌉₊ ≤ ⌈T * 2 ^ n⌉₊ := Nat.ceil_mono (by gcongr)
    have := hk1 n; omega
  have hstep : ∀ n, stepCount N C A T n ω s e
      = N.N ω (C ∩ Set.Ioc (0 : ℝ) ((k n : ℝ) / 2 ^ n) ×ˢ Set.univ) := by
    intro n
    unfold stepCount
    rw [Finset.sum_eq_single_of_mem (k n) (Finset.mem_range.mpr (hkT n))]
    · rw [Set.indicator_of_mem ((hmem n (k n)).mpr rfl)]
    · intro i _ hi
      rw [Set.indicator_of_notMem (fun h => hi ((hmem n i).mp h))]
  unfold strictCount
  simp_rw [hstep]
  apply le_antisymm
  · refine iSup_le (fun n => measure_mono ?_)
    refine Set.inter_subset_inter_right _ (Set.prod_mono ?_ le_rfl)
    intro x ⟨hx0, hx1⟩
    refine ⟨hx0, lt_of_le_of_lt hx1 ?_⟩
    rw [div_lt_iff₀ (by positivity)]; exact hklt n
  · -- continuity from below along `(0, s - 2^{-m}]`
    have hU : C ∩ Set.Ioo (0 : ℝ) s ×ˢ Set.univ
        = ⋃ m : ℕ, C ∩ Set.Ioc (0 : ℝ) (s - (1 / 2) ^ m) ×ˢ Set.univ := by
      ext ⟨x, y⟩
      simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioo, Set.mem_univ, and_true,
        Set.mem_iUnion, Set.mem_Ioc]
      constructor
      · rintro ⟨hc, hx0, hxs⟩
        obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (sub_pos.mpr hxs) (by norm_num : (1 / 2 : ℝ) < 1)
        exact ⟨m, hc, hx0, by linarith⟩
      · rintro ⟨m, hc, hx0, hxm⟩
        exact ⟨hc, hx0, lt_of_le_of_lt hxm (sub_lt_self s (by positivity))⟩
    have hmono : Monotone (fun m : ℕ => C ∩ Set.Ioc (0 : ℝ) (s - (1 / 2) ^ m) ×ˢ Set.univ) := by
      intro a b hab
      refine Set.inter_subset_inter_right _ (Set.prod_mono (Set.Ioc_subset_Ioc_right ?_) le_rfl)
      have : ((1 : ℝ) / 2) ^ b ≤ (1 / 2) ^ a := pow_le_pow_of_le_one (by norm_num) (by norm_num) hab
      linarith
    rw [hU, hmono.measure_iUnion]
    refine iSup_mono (fun m => measure_mono ?_)
    refine Set.inter_subset_inter_right _ (Set.prod_mono (Set.Ioc_subset_Ioc_right ?_) le_rfl)
    have h2 : (0 : ℝ) < 2 ^ m := by positivity
    rw [le_div_iff₀ h2, sub_mul, one_div_pow, div_mul_cancel₀ _ h2.ne']
    linarith [hkge m]
