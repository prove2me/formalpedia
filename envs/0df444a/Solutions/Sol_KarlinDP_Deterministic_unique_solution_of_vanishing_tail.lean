-- Prove2me | solution 1 for KarlinDP.Deterministic.unique_solution_of_vanishing_tail
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T06:02:41.726472+00:00
-- url     : https://prove2.me/submissions/1f99c2ab-4524-42a4-9b0d-feab45cc21f4

import Mathlib
import Definitions.Def_KarlinDP_Deterministic_Model

set_option autoImplicit false

open KarlinDP.Deterministic in
theorem solution {Ω D : Type*} [TopologicalSpace Ω] [T2Space Ω]
    [TopologicalSpace D] [CompactSpace D] [T2Space D] [Nonempty D]
    (L : Ω → D → ℝ) (T : D → Ω → Ω) (P : D → ℝ)
    (hL0 : ∀ ω δ, 0 ≤ L ω δ) (hL : Continuous (fun p : Ω × D => L p.1 p.2))
    (hT : Continuous (fun p : D × Ω => T p.1 p.2))
    (hP0 : ∀ δ, 0 < P δ) (hP : Continuous P)
    (hunif : ∀ ω, TendstoUniformly (fun k s => partialYield L T P ω s k) (totalYield L T P ω)
      Filter.atTop)
    (M : Ω → ℝ)
    (hM : ∀ ω, IsGreatest (Set.range fun δ => L ω δ + P δ * M (T δ ω)) (M ω))
    (htail : ∀ ω, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ s : ℕ → D,
      |M (trajectory T ω s n)| * weight P s n ≤ ε) :
    ∀ ω, IsGreatest (Set.range (totalYield L T P ω)) (M ω) := by
  have hw_succ : ∀ (s : ℕ → D) (n : ℕ), weight P s (n + 1) = weight P s n * P (s n) := by
    intro s n
    simp [weight, Finset.prod_range_succ]
  have hw_nonneg : ∀ (s : ℕ → D) (n : ℕ), 0 ≤ weight P s n := by
    intro s n
    exact Finset.prod_nonneg (fun i _ => (hP0 (s i)).le)
  have hp_succ : ∀ (ω : Ω) (s : ℕ → D) (n : ℕ), partialYield L T P ω s (n + 1) =
      partialYield L T P ω s n + L (trajectory T ω s n) (s n) * weight P s n := by
    intro ω s n
    simp [partialYield, Finset.sum_range_succ]
  have htr_succ : ∀ (ω : Ω) (s : ℕ → D) (n : ℕ),
      trajectory T ω s (n + 1) = T (s n) (trajectory T ω s n) := by
    intro ω s n
    rfl
  have htail_lim : ∀ (ω : Ω) (s : ℕ → D), Filter.Tendsto
      (fun n => weight P s n * M (trajectory T ω s n)) Filter.atTop (nhds 0) := by
    intro ω s
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := htail ω (ε / 2) (by linarith)
    refine ⟨N, fun n hn => ?_⟩
    have h := hN n hn s
    rw [Real.dist_eq, sub_zero, abs_mul, abs_of_nonneg (hw_nonneg s n), mul_comm]
    linarith
  have hpy_lim : ∀ (ω : Ω) (s : ℕ → D), Filter.Tendsto (fun n => partialYield L T P ω s n)
      Filter.atTop (nhds (totalYield L T P ω s)) := by
    intro ω s
    exact (hunif ω).tendsto_at s
  have hsum_lim : ∀ (ω : Ω) (s : ℕ → D), Filter.Tendsto
      (fun n => partialYield L T P ω s n + weight P s n * M (trajectory T ω s n))
      Filter.atTop (nhds (totalYield L T P ω s)) := by
    intro ω s
    have h := (hpy_lim ω s).add (htail_lim ω s)
    rw [add_zero] at h
    exact h
  intro ω
  constructor
  · choose c hc using fun x => (hM x).1
    let x : ℕ → Ω := fun n => Nat.rec ω (fun _ y => T (c y) y) n
    let s : ℕ → D := fun n => c (x n)
    have hx : ∀ n, trajectory T ω s n = x n := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [htr_succ, ih]
    have heq : ∀ n, M ω = partialYield L T P ω s n + weight P s n * M (trajectory T ω s n) := by
      intro n
      induction n with
      | zero => simp [partialYield, weight, trajectory]
      | succ n ih =>
        rw [ih, hp_succ, hw_succ, htr_succ, hx n]
        have h := hc (x n)
        simp only at h
        have hs : s n = c (x n) := rfl
        rw [hs, ← h]
        ring
    refine ⟨s, ?_⟩
    have h2 : Filter.Tendsto
        (fun n => partialYield L T P ω s n + weight P s n * M (trajectory T ω s n))
        Filter.atTop (nhds (M ω)) := by
      have hfun : (fun n => partialYield L T P ω s n + weight P s n * M (trajectory T ω s n))
          = fun _ => M ω := by
        funext n
        exact (heq n).symm
      rw [hfun]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique (hsum_lim ω s) h2
  · rintro _ ⟨s, rfl⟩
    have hle : ∀ n, partialYield L T P ω s n + weight P s n * M (trajectory T ω s n) ≤ M ω := by
      intro n
      induction n with
      | zero => simp [partialYield, weight, trajectory]
      | succ n ih =>
        refine le_trans ?_ ih
        rw [hp_succ, hw_succ, htr_succ]
        have h := (hM (trajectory T ω s n)).2 ⟨s n, rfl⟩
        have hw := hw_nonneg s n
        have hm := mul_le_mul_of_nonneg_left h hw
        nlinarith [hm]
    exact le_of_tendsto' (hsum_lim ω s) hle
