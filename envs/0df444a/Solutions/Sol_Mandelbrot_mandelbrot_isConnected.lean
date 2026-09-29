-- Prove2me | solution 1 for Mandelbrot.mandelbrot_isConnected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-15T21:48:02.529335+00:00
-- url     : https://prove2.me/submissions/7c23c812-c120-4fd8-aca1-fd1595b95b05
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_mandelbrot_sets
import Theorems.Thm_Mandelbrot_mandelbrot_escape_criterion
import Theorems.Thm_Mandelbrot_mandelbrot_lemniscate_isPreconnected
import Theorems.Thm_isPreconnected_iInter_of_antitone_isCompact

open Topology Set Function Filter Bornology Metric MeasureTheory

open Mandelbrot in
theorem solution : IsConnected mandelbrotSet := by
  -- `P k c` is the `k`-th point of the critical orbit of `z ↦ z ^ 2 + c`.
  set P : ℕ → ℂ → ℂ := fun k c => (fun z ↦ z ^ 2 + c)^[k] 0 with hPdef
  have hP0 : ∀ c : ℂ, P 0 c = 0 := fun c => rfl
  have hPsucc : ∀ (k : ℕ) (c : ℂ), P (k + 1) c = (P k c) ^ 2 + c := by
    intro k c
    simp [hPdef, Function.iterate_succ_apply']
  set L : ℕ → Set ℂ := fun k => {c : ℂ | ‖P k c‖ ≤ 2} with hLdef
  -- The Mandelbrot set is the intersection of the lemniscate domains.
  have hM : mandelbrotSet = ⋂ k, L k := by
    rw [mandelbrot_escape_criterion]
    ext c
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact Iff.rfl
  -- Each `P k` is continuous in the parameter.
  have hcont : ∀ k : ℕ, Continuous (P k) := by
    intro k
    induction k with
    | zero =>
        have : (P 0) = fun _ : ℂ => (0 : ℂ) := funext hP0
        rw [this]; exact continuous_const
    | succ m ih =>
        have : (P (m + 1)) = fun c => (P m c) ^ 2 + c := funext (hPsucc m)
        rw [this]
        exact (ih.pow 2).add continuous_id
  -- Each lemniscate domain is closed.
  have hclosed : ∀ k : ℕ, IsClosed (L k) :=
    fun k => isClosed_le ((hcont k).norm) continuous_const
  -- A basic estimate: `‖a ^ 2 + b‖ ≥ ‖a‖ ^ 2 - ‖b‖`.
  have hest : ∀ a b : ℂ, ‖a‖ ^ 2 - ‖b‖ ≤ ‖a ^ 2 + b‖ := by
    intro a b
    have h := norm_sub_norm_le (a ^ 2) (-b)
    simpa [norm_pow, sub_neg_eq_add] using h
  -- If `‖c‖ > 2` the critical orbit escapes: every later point has modulus `> 2`.
  have hgrow : ∀ c : ℂ, 2 < ‖c‖ → ∀ k : ℕ, ‖c‖ ≤ ‖P (k + 1) c‖ ∧ 2 < ‖P (k + 1) c‖ := by
    intro c hc k
    induction k with
    | zero =>
        have : P 1 c = c := by rw [hPsucc 0 c, hP0]; ring
        rw [this]
        exact ⟨le_rfl, hc⟩
    | succ m ih =>
        obtain ⟨ih1, ih2⟩ := ih
        have hle : ‖P (m + 1) c‖ ^ 2 - ‖c‖ ≤ ‖P (m + 2) c‖ := by
          rw [hPsucc (m + 1) c]; exact hest _ _
        have h2 : (2 : ℝ) < ‖P (m + 1) c‖ := ih2
        have hkey : ‖P (m + 1) c‖ < ‖P (m + 1) c‖ ^ 2 - ‖c‖ := by nlinarith
        exact ⟨le_trans ih1 (le_of_lt (lt_of_lt_of_le hkey hle)),
          lt_of_lt_of_le (lt_trans h2 hkey) hle⟩
  -- Hence every lemniscate domain of positive index lies in the closed disk of radius 2.
  have hball : ∀ k : ℕ, L (k + 1) ⊆ Metric.closedBall (0 : ℂ) 2 := by
    intro k c hcmem
    simp only [Metric.mem_closedBall, dist_zero_right]
    by_contra hcon
    push Not at hcon
    exact absurd hcmem (not_le.2 ((hgrow c hcon k).2))
  -- Compactness.
  have hcompact : ∀ k : ℕ, IsCompact (L (k + 1)) := by
    intro k
    exact Metric.isCompact_of_isClosed_isBounded (hclosed (k + 1))
      ((Metric.isBounded_closedBall).subset (hball k))
  -- The lemniscate domains are nested.
  have hstep : ∀ k : ℕ, L (k + 1) ⊆ L k := by
    intro k c hcmem
    have hc2 : ‖c‖ ≤ 2 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hball k hcmem
    by_contra hcon
    have hgt : (2 : ℝ) < ‖P k c‖ := lt_of_not_ge hcon
    have hle : ‖P k c‖ ^ 2 - ‖c‖ ≤ ‖P (k + 1) c‖ := by
      rw [hPsucc k c]; exact hest _ _
    have : (2 : ℝ) < ‖P (k + 1) c‖ := by nlinarith
    exact absurd hcmem (not_le.2 this)
  have hanti : Antitone fun k => L (k + 1) :=
    antitone_nat_of_succ_le fun k => hstep (k + 1)
  -- Dropping the index-zero (trivial) term does not change the intersection.
  have hshift : (⋂ k, L k) = ⋂ k, L (k + 1) := by
    refine Set.Subset.antisymm (fun x hx => Set.mem_iInter.2 fun k =>
      Set.mem_iInter.1 hx (k + 1)) (fun x hx => Set.mem_iInter.2 fun k => ?_)
    match k with
    | 0 => simp [hLdef, hP0]
    | (m + 1) => exact Set.mem_iInter.1 hx m
  refine ⟨⟨0, ?_⟩, ?_⟩
  · -- `0` belongs to the Mandelbrot set.
    have hzero : ∀ k : ℕ, P k 0 = 0 := by
      intro k
      induction k with
      | zero => exact hP0 0
      | succ m ih => rw [hPsucc m 0, ih]; ring
    rw [hM]
    exact Set.mem_iInter.2 fun k => by simp [hLdef, hzero k]
  · rw [hM, hshift]
    exact isPreconnected_iInter_of_antitone_isCompact hanti hcompact
      (fun k => mandelbrot_lemniscate_isPreconnected (k + 1))
