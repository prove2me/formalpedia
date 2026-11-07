-- Prove2me | solution 1 for HeymanStidham.HLG.eq3_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T18:32:53.543652+00:00
-- url     : https://prove2.me/submissions/f7867d33-3510-41f0-a7de-1e158a483a13

import Mathlib
import Definitions.Def_HeymanStidham_HLG_Setting

open Filter Topology MeasureTheory

namespace Aux_HLG_EQ3
open HeymanStidham.HLG

theorem rate_eq (g : ℕ → ℝ → ℝ) (N : ℕ) (T : ℝ)
    (hz : ∀ n, N ≤ n → ∀ τ ∈ Set.Icc 0 T, g n τ = 0) :
    Set.EqOn (fun τ => ∑ n ∈ Finset.range N, g n τ) (rate g) (Set.Icc 0 T) := by
  intro τ hτ
  simp only [rate]
  rw [tsum_eq_sum (s := Finset.range N)]
  intro n hn
  exact hz n (by simpa using hn) τ hτ

theorem rate_int (g : ℕ → ℝ → ℝ) (N : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (hi : ∀ n, IntervalIntegrable (g n) volume 0 T)
    (hz : ∀ n, N ≤ n → ∀ τ ∈ Set.Icc 0 T, g n τ = 0) :
    IntervalIntegrable (rate g) volume 0 T ∧
      (∫ τ in (0 : ℝ)..T, rate g τ) = ∑ n ∈ Finset.range N, ∫ τ in (0 : ℝ)..T, g n τ := by
  have hS : IntervalIntegrable (fun τ => ∑ n ∈ Finset.range N, g n τ) volume 0 T := by
    have := IntervalIntegrable.sum (Finset.range N) (fun n _ => hi n)
    have e : (∑ n ∈ Finset.range N, g n) = (fun τ => ∑ n ∈ Finset.range N, g n τ) := by
      funext τ; simp [Finset.sum_apply]
    rwa [e] at this
  have hEq := rate_eq g N T hz
  constructor
  · refine hS.congr ?_
    intro τ hτ
    apply hEq
    rw [Set.uIoc_of_le hT] at hτ
    exact ⟨hτ.1.le, hτ.2⟩
  · rw [← intervalIntegral.integral_finsetSum (fun n _ => hi n)]
    refine intervalIntegral.integral_congr ?_
    intro τ hτ
    rw [Set.uIcc_of_le hT] at hτ
    exact (hEq hτ).symm

end Aux_HLG_EQ3

open HeymanStidham.HLG Aux_HLG_EQ3 in
theorem solution (t : ℕ → ℝ) (ht : Monotone t) (ht0 : 0 ≤ t 0)
    (htinf : Tendsto t atTop atTop)
    (f : ℕ → ℝ → ℝ) (s : ℕ → ℝ) (hI : CondI t f s)
    (hiii : ∀ n τ, 0 ≤ τ → 0 ≤ f n τ)
    (hiv : ∀ n, IntegrableOn (f n) (Set.Ici 0))
    (T : ℝ) (hT : 0 ≤ T) :
    IntervalIntegrable (rate f) volume 0 T ∧
      finishedTotal t s (custTotal f) T ≤ ∫ τ in (0 : ℝ)..T, rate f τ ∧
      ∫ τ in (0 : ℝ)..T, rate f τ ≤ arrivedTotal t (custTotal f) T := by
  obtain ⟨N, hN⟩ := (htinf.eventually_gt_atTop T).exists_forall_of_atTop
  -- customers that have not arrived by `T` contribute nothing on `[0, T]`
  have hzero : ∀ n, T < t n → ∀ τ ∈ Set.Icc 0 T, f n τ = 0 := by
    intro n hn τ hτ
    apply hI.2 n τ hτ.1
    intro hm
    linarith [hm.1, hτ.2]
  have hz : ∀ n, N ≤ n → ∀ τ ∈ Set.Icc 0 T, f n τ = 0 := fun n hn => hzero n (hN n hn)
  have hfi : ∀ n, IntervalIntegrable (f n) volume 0 T := by
    intro n
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    exact (hiv n).mono_set (fun x hx => le_of_lt hx.1)
  obtain ⟨C1, C2⟩ := rate_int f N T hT hfi hz
  -- `F_n(T) ≤ g_n`
  have hFle : ∀ n, (∫ τ in (0 : ℝ)..T, f n τ) ≤ custTotal f n := by
    intro n
    rw [intervalIntegral.integral_of_le hT]
    unfold custTotal
    refine setIntegral_mono_set (hiv n) ?_ (HasSubset.Subset.eventuallyLE
      (fun x hx => (show x ∈ Set.Ici (0:ℝ) from le_of_lt hx.1)))
    exact (ae_restrict_iff' measurableSet_Ici).2 (Eventually.of_forall fun τ hτ => hiii n τ hτ)
  -- `F_n(T) ≥ 0`
  have hF0 : ∀ n, 0 ≤ ∫ τ in (0 : ℝ)..T, f n τ := fun n =>
    intervalIntegral.integral_nonneg hT (fun τ hτ => hiii n τ hτ.1)
  -- `F_n(T) = 0` if `T < t_n`
  have hFz : ∀ n, T < t n → (∫ τ in (0 : ℝ)..T, f n τ) = 0 := by
    intro n hn
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) (fun τ hτ => by
      rw [Set.uIcc_of_le hT] at hτ; exact hzero n hn τ hτ)]
    simp
  -- `F_n(T) = g_n` if `t_n + s_n ≤ T`
  have hFeq : ∀ n, t n + s n ≤ T → (∫ τ in (0 : ℝ)..T, f n τ) = custTotal f n := by
    intro n hn
    rw [intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc]
    unfold custTotal
    refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ici
      (fun x hx => hx.1) ?_).symm
    intro τ hτ
    apply hI.2 n τ hτ.1
    intro hm
    have : τ ∉ Set.Icc 0 T := hτ.2
    exact this ⟨hτ.1, hm.2.trans hn⟩
  have hU : arrivedTotal t (custTotal f) T =
      ∑ n ∈ Finset.range N, Set.indicator {n : ℕ | t n ≤ T} (custTotal f) n := by
    unfold arrivedTotal
    refine tsum_eq_sum (fun n hn => ?_)
    have : N ≤ n := by simpa using hn
    refine Set.indicator_of_notMem ?_ _
    simp only [Set.mem_setOf_eq, not_le]
    exact hN n this
  have hV : finishedTotal t s (custTotal f) T =
      ∑ n ∈ Finset.range N, Set.indicator {n : ℕ | t n + s n ≤ T} (custTotal f) n := by
    unfold finishedTotal
    refine tsum_eq_sum (fun n hn => ?_)
    have : N ≤ n := by simpa using hn
    refine Set.indicator_of_notMem ?_ _
    simp only [Set.mem_setOf_eq, not_le]
    linarith [hN n this, hI.1 n]
  refine ⟨C1, ?_, ?_⟩
  · rw [C2, hV]
    refine Finset.sum_le_sum (fun n _ => ?_)
    by_cases hB : n ∈ {n : ℕ | t n + s n ≤ T}
    · rw [Set.indicator_of_mem hB, hFeq n hB]
    · rw [Set.indicator_of_notMem hB]; exact hF0 n
  · rw [C2, hU]
    refine Finset.sum_le_sum (fun n _ => ?_)
    by_cases hA : n ∈ {n : ℕ | t n ≤ T}
    · rw [Set.indicator_of_mem hA]; exact hFle n
    · rw [Set.indicator_of_notMem hA]
      simp only [Set.mem_setOf_eq, not_le] at hA
      rw [hFz n hA]
