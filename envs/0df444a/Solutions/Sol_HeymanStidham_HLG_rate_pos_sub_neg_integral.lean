-- Prove2me | solution 1 for HeymanStidham.HLG.rate_pos_sub_neg_integral
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:05:14.306025+00:00
-- url     : https://prove2.me/submissions/04d6a640-3241-4198-8114-4939cfe8920d

import Mathlib
import Definitions.Def_HeymanStidham_HLG_Setting

open HeymanStidham.HLG
open Filter Topology MeasureTheory
namespace Aux_HeymanStidham_RPSN
open HeymanStidham.HLG MeasureTheory

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

end Aux_HeymanStidham_RPSN

theorem solution (t : ℕ → ℝ) (ht : Monotone t) (ht0 : 0 ≤ t 0)
    (htinf : Tendsto t atTop atTop)
    (f : ℕ → ℝ → ℝ) (s : ℕ → ℝ) (hI : CondI t f s)
    (hv : ∀ n, IntegrableOn (f n) (Set.Ici 0))
    (T : ℝ) (hT : 0 ≤ T) :
    IntervalIntegrable (rate (posPartFn f)) volume 0 T ∧
      IntervalIntegrable (rate (negPartFn f)) volume 0 T ∧
      IntervalIntegrable (rate f) volume 0 T ∧
      (∫ τ in (0 : ℝ)..T, rate (posPartFn f) τ) - (∫ τ in (0 : ℝ)..T, rate (negPartFn f) τ) =
        ∫ τ in (0 : ℝ)..T, rate f τ := by
  open Aux_HeymanStidham_RPSN in
  obtain ⟨N, hN⟩ := (htinf.eventually_gt_atTop T).exists_forall_of_atTop
  have hz : ∀ n, N ≤ n → ∀ τ ∈ Set.Icc 0 T, f n τ = 0 := by
    intro n hn τ hτ
    apply hI.2 n τ hτ.1
    intro hm
    have := hN n hn
    linarith [hm.1, hτ.2]
  have hfi : ∀ n, IntervalIntegrable (f n) volume 0 T := by
    intro n
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    exact (hv n).mono_set (fun x hx => le_of_lt hx.1)
  have hpi : ∀ n, IntervalIntegrable (posPartFn f n) volume 0 T := by
    intro n
    have h := hfi n
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT] at h ⊢
    have := h.pos_part
    have e : posPartFn f n = fun a => max (f n a) 0 := by
      funext a; simp [posPartFn, max_comm]
    rw [e]; exact this
  have hni : ∀ n, IntervalIntegrable (negPartFn f n) volume 0 T := by
    intro n
    have h := hfi n
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT] at h ⊢
    have := h.neg_part
    have e : negPartFn f n = fun a => max (-f n a) 0 := by
      funext a; simp [negPartFn, max_comm]
    rw [e]; exact this
  have hpz : ∀ n, N ≤ n → ∀ τ ∈ Set.Icc 0 T, posPartFn f n τ = 0 := by
    intro n hn τ hτ; simp [posPartFn, hz n hn τ hτ]
  have hnz : ∀ n, N ≤ n → ∀ τ ∈ Set.Icc 0 T, negPartFn f n τ = 0 := by
    intro n hn τ hτ; simp [negPartFn, hz n hn τ hτ]
  obtain ⟨A1, A2⟩ := rate_int _ N T hT hpi hpz
  obtain ⟨B1, B2⟩ := rate_int _ N T hT hni hnz
  obtain ⟨C1, C2⟩ := rate_int _ N T hT hfi hz
  refine ⟨A1, B1, C1, ?_⟩
  rw [A2, B2, C2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [← intervalIntegral.integral_sub (hpi n) (hni n)]
  congr 1
  ext τ
  simp only [posPartFn, negPartFn]
  rcases le_total 0 (f n τ) with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
