-- Prove2me | solution 1 for LeiBR.Sync.eq_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T11:51:33.83452+00:00
-- url     : https://prove2.me/submissions/c497ee5f-3f6a-41db-9b50-c304bb8379a5

import Mathlib
import Definitions.Def_LeiBR_Sync_NashGame
import Definitions.Def_LeiBR_Sync_StochGame
import Theorems.Thm_LeiBR_Sync_eq_5

open MeasureTheory

open LeiBR.Sync in
theorem solution
    {N : ℕ} {n : Fin N → ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {d : ℕ} (ξ : Ω → EuclideanSpace ℝ (Fin d))
    (X : ∀ i : Fin N, Set (Strat n i)) (ψ : Fin N → Profile n → EuclideanSpace ℝ (Fin d) → ℝ)
    (gψ : ∀ i : Fin N, Profile n → EuclideanSpace ℝ (Fin d) → Strat n i) (M : Fin N → ℝ)
    (hA1 : Assumption1 P ξ X ψ gψ M) (μ : ℝ) (hμ : 0 < μ)
    (xhat : Profile n → Profile n) (hxhat : IsProxBR X (payoff P ξ ψ) μ xhat)
    (hA2 : Assumption2 X (payoff P ξ ψ) μ) :
    ∀ y ∈ stratSet X, ∀ y' ∈ stratSet X,
      blockDist (xhat y') (xhat y) ≤ specNorm (Gamma X (payoff P ξ ψ) μ) * blockDist y' y := by
  intro y hy y' hy'
  set G := Gamma X (payoff P ξ ψ) μ with hG
  set v : Fin N → ℝ := fun j => ‖y' j - y j‖ with hv
  have h5 : ∀ i, ‖xhat y' i - xhat y i‖ ≤ (G.mulVec v) i := fun i => by
    simpa [Matrix.mulVec, dotProduct] using
      eq_5 P ξ X ψ gψ M hA1 μ hμ xhat hxhat y hy y' hy' i
  have hop := (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin N) G).le_opNorm (WithLp.toLp 2 v)
  rw [Matrix.toEuclideanCLM_toLp, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq] at hop
  have hL : blockDist (xhat y') (xhat y) ≤ Real.sqrt (∑ i, ‖(G.mulVec v) i‖ ^ 2) := by
    unfold blockDist
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
    rw [Real.norm_eq_abs, sq_abs]
    exact pow_le_pow_left₀ (norm_nonneg _) (h5 i) 2
  have hR : blockDist y' y = Real.sqrt (∑ i, ‖v i‖ ^ 2) := by
    unfold blockDist
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hv, Real.norm_eq_abs, sq_abs]
  rw [hR]
  exact hL.trans (by simpa [specNorm] using hop)
