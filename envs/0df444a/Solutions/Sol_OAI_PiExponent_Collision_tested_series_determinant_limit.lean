-- Prove2me | solution 1 for OAI.PiExponent.Collision.tested_series_determinant_limit
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T19:11:48.145989+00:00
-- url     : https://prove2.me/submissions/55775c5e-4fbe-4f40-8f12-6467e1e21cc2

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.OrderClosed

open scoped BigOperators Topology
open Filter

/-- Determinant bounds pass to the limit of a tested series: if every entry is the sum of a
series and all finite truncation determinants are bounded by `K`, then the determinant of the
limit matrix is bounded by `K`. -/
theorem solution {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (B : ι → ℕ → ℂ) (C : κ → ℕ → ι → ℂ)
    (T : Matrix ι ι ℂ)
    (hsum : ∀ r c, HasSum (fun d => B r d * C (group r) d c) (T r c))
    (K : ℝ)
    (hbound : ∀ N, ‖Matrix.det (fun r c =>
      ∑ d ∈ Finset.range N, B r d * C (group r) d c)‖ ≤ K) :
    ‖T.det‖ ≤ K := by
  have hlim : ∀ r c, Tendsto (fun N => ∑ d ∈ Finset.range N,
      B r d * C (group r) d c) atTop (𝓝 (T r c)) :=
    fun r c => (hsum r c).tendsto_sum_nat
  have hmatrix : Tendsto (fun N : ℕ =>
      (fun r c => ∑ d ∈ Finset.range N, B r d * C (group r) d c)) atTop (𝓝 T) := by
    apply tendsto_pi_nhds.mpr
    intro r
    apply tendsto_pi_nhds.mpr
    intro c
    exact hlim r c
  have hdet : Tendsto (fun N : ℕ => Matrix.det (fun r c =>
      ∑ d ∈ Finset.range N, B r d * C (group r) d c)) atTop (𝓝 T.det) := by
    have hcont : Continuous (fun M : Matrix ι ι ℂ => M.det) :=
      Continuous.matrix_det continuous_id
    exact (hcont.tendsto T).comp hmatrix
  exact le_of_tendsto' hdet.norm hbound
