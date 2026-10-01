-- Prove2me | solution 1 for MilnorDynamics.exists_subseq_tendsto_of_bounded_on_countable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T00:44:05.531193+00:00
-- url     : https://prove2.me/submissions/be9d56dd-18cb-489f-bece-efd688e3a97a

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set
open MilnorDynamics

/-- Variant 1: the values on the countable set live in a product of compact
discs, which is compact by Tychonoff and first countable, so the sequence of
coordinate functions has a convergent subsequence. -/
theorem solution (D : ℕ → ℂ) (f : ℕ → ℂ → ℂ)
    (hb : ∀ k, ∃ M, ∀ n, ‖f n (D k)‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ g : ℕ → ℂ, ∀ k, Tendsto (fun n => f (φ n) (D k)) atTop (nhds (g k)) := by
  choose M hM using hb
  have hcpt : ∀ k, IsCompact (Metric.closedBall (0 : ℂ) (M k)) := fun k =>
    Metric.isCompact_iff_isClosed_bounded.mpr
      ⟨Metric.isClosed_closedBall, Metric.isBounded_closedBall⟩
  have hK : IsCompact {u : ℕ → ℂ | ∀ k, u k ∈ Metric.closedBall (0 : ℂ) (M k)} := by
    simpa [Set.pi] using isCompact_univ_pi hcpt
  have hmem : ∀ n,
      (fun k => f n (D k)) ∈ {u : ℕ → ℂ | ∀ k, u k ∈ Metric.closedBall (0 : ℂ) (M k)} := by
    intro n k
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hM k n
  obtain ⟨g, _hg, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  exact ⟨φ, hφ, g, fun k => tendsto_pi_nhds.mp hlim k⟩
