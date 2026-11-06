-- Prove2me | solution 1 for LeiBR.Rand.eq9_contraction
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T10:49:16.482648+00:00
-- url     : https://prove2.me/submissions/79daef81-a986-48f4-a94f-4738a2767ee0

import Theorems.Thm_LeiBR_Rand_eq5_gamma_contraction
open MeasureTheory ProbabilityTheory
open LeiBR.Rand

theorem solution {N : ℕ} {n : Fin N → ℕ} {d : ℕ} (G : Game N n)
    (μξ : Measure (EuclideanSpace ℝ (Fin d)))
    (ψ : Fin N → LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → ℝ)
    (gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i) (M : Fin N → ℝ)
    (hA1 : Assumption1 G μξ ψ gψ M) (mu : ℝ) (hmu : 0 < mu)
    (xhat : LeiBR.Sync.Profile n → LeiBR.Sync.Profile n) (hxhat : IsProxBR G mu xhat)
    (hA2 : Assumption2 G mu) (y y' : LeiBR.Sync.Profile n) (hy : G.Feasible y) (hy' : G.Feasible y') :
    blockNorm (xhat y' - xhat y) ≤ contrFactor G mu * blockNorm (y' - y) := by
  set u : Fin N → ℝ := fun i => ‖xhat y' i - xhat y i‖ with hu
  set v : Fin N → ℝ := fun j => ‖y' j - y j‖ with hv
  have h5 : ∀ i, u i ≤ ((Gamma G mu).mulVec v) i := fun i => by
    simpa [Matrix.mulVec, dotProduct] using
      eq5_gamma_contraction G μξ ψ gψ M hA1 mu hmu xhat hxhat y y' hy hy' i
  have hop := (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin N) (Gamma G mu)).le_opNorm
    (WithLp.toLp 2 v)
  rw [Matrix.toEuclideanCLM_toLp, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq] at hop
  have hL : blockNorm (xhat y' - xhat y) ≤ Real.sqrt (∑ i, ‖((Gamma G mu).mulVec v) i‖ ^ 2) := by
    unfold blockNorm
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
    rw [Real.norm_eq_abs, sq_abs, Pi.sub_apply]
    exact pow_le_pow_left₀ (norm_nonneg _) (h5 i) 2
  have hR : blockNorm (y' - y) = Real.sqrt (∑ i, ‖v i‖ ^ 2) := by
    unfold blockNorm
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hv, Real.norm_eq_abs, sq_abs, Pi.sub_apply]
  rw [hR]
  exact hL.trans (by simpa [contrFactor] using hop)
