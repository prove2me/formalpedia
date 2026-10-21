-- Prove2me | solution 1 for IteratedFDeriv.exists_diagonal_tendstoUniformlyOn
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-20T16:59:05.331893+00:00
-- url     : https://prove2.me/submissions/5b9c6eb7-e750-4e15-b0d5-58861209d0f8

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Order.Filter.Finite

open Filter Metric

namespace IteratedFDeriv

/-- Diagonal extraction for `C^∞_loc` convergence: if `fk k → f` and, for each `k`,
`g k j → fk k` (as `j → ∞`) in `C^∞_loc`, then some diagonal `g k (φ k)` tends to `f`. -/
theorem exists_diagonal_tendstoUniformlyOn_iteratedFDeriv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (fk : ℕ → E → F) (g : ℕ → ℕ → E → F)
    (hf : ∀ m : ℕ, ∀ K : Set E, IsCompact K →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (fk k)) (iteratedFDeriv ℝ m f) atTop K)
    (hg : ∀ k m : ℕ, ∀ K : Set E, IsCompact K →
      TendstoUniformlyOn (fun j => iteratedFDeriv ℝ m (g k j)) (iteratedFDeriv ℝ m (fk k))
        atTop K) :
    ∃ φ : ℕ → ℕ, ∀ m : ℕ, ∀ K : Set E, IsCompact K →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (g k (φ k))) (iteratedFDeriv ℝ m f)
        atTop K := by
  have key : ∀ k : ℕ, ∃ j : ℕ, ∀ m ≤ k, ∀ x ∈ closedBall (0 : E) k,
      dist (iteratedFDeriv ℝ m (fk k) x) (iteratedFDeriv ℝ m (g k j) x) < 1 / ((k : ℝ) + 1) := by
    intro k
    have h : ∀ m ∈ Finset.range (k + 1), ∀ᶠ j in atTop, ∀ x ∈ closedBall (0 : E) k,
        dist (iteratedFDeriv ℝ m (fk k) x) (iteratedFDeriv ℝ m (g k j) x) <
          1 / ((k : ℝ) + 1) := fun m _ =>
      (Metric.tendstoUniformlyOn_iff.1 (hg k m _ (isCompact_closedBall 0 k))) _ (by positivity)
    obtain ⟨j, hj⟩ := ((Filter.eventually_all_finset _).2 h).exists
    exact ⟨j, fun m hm x hx => hj m (Finset.mem_range.2 (by omega)) x hx⟩
  choose φ hφ using key
  refine ⟨φ, fun m K hK => ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  have h1 := (Metric.tendstoUniformlyOn_iff.1 (hf m K hK)) (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (half_pos hε)
  have h2 : ∀ᶠ k : ℕ in atTop, m ≤ k ∧ R ≤ (k : ℝ) ∧ N ≤ k :=
    (eventually_ge_atTop m).and
      ((tendsto_natCast_atTop_atTop.eventually_ge_atTop R).and (eventually_ge_atTop N))
  filter_upwards [h1, h2] with k hk1 hk2 x hx
  obtain ⟨hmk, hRk, hNk⟩ := hk2
  have hx' : x ∈ closedBall (0 : E) k := closedBall_subset_closedBall hRk (hR hx)
  have h3 := hφ k m hmk x hx'
  have h4 : 1 / ((k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
    gcongr
  calc dist (iteratedFDeriv ℝ m f x) (iteratedFDeriv ℝ m (g k (φ k)) x)
      ≤ dist (iteratedFDeriv ℝ m f x) (iteratedFDeriv ℝ m (fk k) x) +
        dist (iteratedFDeriv ℝ m (fk k) x) (iteratedFDeriv ℝ m (g k (φ k)) x) :=
        dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hk1 x hx) (by linarith)
    _ = ε := by ring

end IteratedFDeriv

open IteratedFDeriv

theorem solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (fk : ℕ → E → F) (g : ℕ → ℕ → E → F)
    (hf : ∀ m : ℕ, ∀ K : Set E, IsCompact K →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (fk k)) (iteratedFDeriv ℝ m f) Filter.atTop K)
    (hg : ∀ k m : ℕ, ∀ K : Set E, IsCompact K →
      TendstoUniformlyOn (fun j => iteratedFDeriv ℝ m (g k j)) (iteratedFDeriv ℝ m (fk k))
        Filter.atTop K) :
    ∃ φ : ℕ → ℕ, ∀ m : ℕ, ∀ K : Set E, IsCompact K →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (g k (φ k))) (iteratedFDeriv ℝ m f)
        Filter.atTop K :=
  exists_diagonal_tendstoUniformlyOn_iteratedFDeriv f fk g hf hg
