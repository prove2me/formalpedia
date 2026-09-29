-- Prove2me | solution 1 for NonsmoothNewton.Global.limit_is_root
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:04:49.98086+00:00
-- url     : https://prove2.me/submissions/095e63d4-4e35-4b7e-a6a6-5b7b955d92c8

import Mathlib
import Definitions.Def_NonsmoothNewton_Global_dirDeriv
import Definitions.Def_NonsmoothNewton_Global_clarkeJac
import Definitions.Def_NonsmoothNewton_Global_SemismoothAt
import Definitions.Def_NonsmoothNewton_Global_IsNewtonRun



namespace NonsmoothNewton.Global

open Filter Topology

theorem lir_core {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (x0 : EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (hF : LocallyLipschitz F)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (V : ℕ → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hrun : IsNewtonRun F x V) (hS : ∀ k, x k ∈ Metric.closedBall x0 r)
    (xstar : EuclideanSpace ℝ (Fin n)) (hlim : Tendsto x atTop (𝓝 xstar)) :
    (∃ C : ℝ, ∀ k, ‖V k‖ ≤ C) ∧ xstar ∈ Metric.closedBall x0 r ∧ F xstar = 0 := by
  obtain ⟨K, hK⟩ := (hF.locallyLipschitzOn (s := Metric.closedBall x0 (r + 1))).exists_lipschitzOnWith_of_compact
    (isCompact_closedBall x0 (r + 1))
  have hK' : LipschitzOnWith K F (Metric.ball x0 (r + 1)) := hK.mono Metric.ball_subset_closedBall
  have hder : ∀ u ∈ Metric.ball x0 (r + 1), ‖fderiv ℝ F u‖ ≤ K := fun u hu =>
    norm_fderiv_le_of_lipschitzOn ℝ (Metric.isOpen_ball.mem_nhds hu) hK'
  have hbJ : ∀ z ∈ Metric.closedBall x0 r, bJac F z ⊆ Metric.closedBall 0 (K : ℝ) := by
    intro z hz W hW
    obtain ⟨u, hu, -, hV⟩ := hW
    have hz' : z ∈ Metric.ball x0 (r + 1) := by
      rw [Metric.mem_closedBall] at hz; rw [Metric.mem_ball]; linarith
    have hev : ∀ᶠ k in atTop, ‖fderiv ℝ F (u k)‖ ≤ K :=
      (hu.eventually (Metric.isOpen_ball.mem_nhds hz')).mono fun k hk => hder _ hk
    rw [mem_closedBall_zero_iff]
    exact le_of_tendsto hV.norm hev
  have hVb : ∀ k, ‖V k‖ ≤ K := by
    intro k
    have := convexHull_min (hbJ _ (hS k)) (convex_closedBall 0 (K : ℝ)) (hrun k).1
    rwa [mem_closedBall_zero_iff] at this
  refine ⟨⟨K, hVb⟩, Metric.isClosed_closedBall.mem_of_tendsto hlim (Eventually.of_forall hS), ?_⟩
  have hlim1 : Tendsto (fun k => x (k + 1)) atTop (𝓝 xstar) := hlim.comp (tendsto_add_atTop_nat 1)
  have hd0 : Tendsto (fun k => x (k + 1) - x k) atTop (𝓝 0) := by
    simpa using hlim1.sub hlim
  have h1 : Tendsto (fun k => F (x k)) atTop (𝓝 (F xstar)) := (hF.continuous.tendsto xstar).comp hlim
  have h2 : Tendsto (fun k => F (x k)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun k => (K : ℝ) * ‖x (k + 1) - x k‖) (fun k => ?_) ?_
    · have : F (x k) = -(V k (x (k + 1) - x k)) := by rw [(hrun k).2, neg_neg]
      rw [this, norm_neg]
      exact ((V k).le_opNorm (x (k + 1) - x k)).trans
        (mul_le_mul_of_nonneg_right (hVb k) (norm_nonneg _))
    · simpa using hd0.norm.const_mul (K : ℝ)
  exact tendsto_nhds_unique h1 h2

end NonsmoothNewton.Global

open NonsmoothNewton.Global
open NonsmoothNewton.Global Filter Topology

theorem solution {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (x0 : EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (hF : LocallyLipschitz F)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (V : ℕ → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hrun : IsNewtonRun F x V) (hS : ∀ k, x k ∈ Metric.closedBall x0 r)
    (xstar : EuclideanSpace ℝ (Fin n)) (hlim : Tendsto x atTop (𝓝 xstar)) :
    (∃ C : ℝ, ∀ k, ‖V k‖ ≤ C) ∧ xstar ∈ Metric.closedBall x0 r ∧ F xstar = 0 := by
  exact lir_core F x0 r hF x V hrun hS xstar hlim
