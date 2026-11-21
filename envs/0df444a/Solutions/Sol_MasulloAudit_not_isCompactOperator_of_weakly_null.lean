-- Prove2me | solution 1 for MasulloAudit.not_isCompactOperator_of_weakly_null
-- status  : ACCEPTED   (prove)
-- author  : @lll
-- created : 2026-11-21T00:30:09.871183+00:00
-- url     : https://prove2.me/submissions/f2cafce3-9f37-4cff-8ca7-e94c7ecfed5e

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Compact.Basic

open Filter Topology

theorem solution {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    {T : E →L[𝕜] F} {x : ℕ → E} {R c : ℝ}
    (hb : ∀ n, ‖x n‖ ≤ R)
    (hw : ∀ y : E, Tendsto (fun n => (inner 𝕜 y (x n) : 𝕜)) atTop (𝓝 0))
    (hc0 : 0 < c) (hc : ∀ᶠ n in atTop, c ≤ ‖T (x n)‖) :
    ¬ IsCompactOperator T := by
  intro hT
  obtain ⟨K, hK, hsub⟩ :=
    IsCompactOperator.image_closedBall_subset_compact (f := (T : E →ₗ[𝕜] F)) hT R
  have hmem : ∀ n, T (x n) ∈ K := fun n =>
    hsub ⟨x n, by simpa using hb n, rfl⟩
  obtain ⟨z, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  have h1 : Tendsto (fun n => (inner 𝕜 z (T (x (φ n))) : 𝕜)) atTop (𝓝 (inner 𝕜 z z)) :=
    tendsto_const_nhds.inner hlim
  have h2 : Tendsto (fun n => (inner 𝕜 z (T (x (φ n))) : 𝕜)) atTop (𝓝 0) := by
    have := (hw (ContinuousLinearMap.adjoint T z)).comp hφ.tendsto_atTop
    refine this.congr fun n => ?_
    simp [Function.comp, ContinuousLinearMap.adjoint_inner_left]
  have hz : z = 0 := inner_self_eq_zero.mp (tendsto_nhds_unique h1 h2)
  subst hz
  have h3 : Tendsto (fun n => ‖T (x (φ n))‖) atTop (𝓝 0) := by
    simpa using hlim.norm
  obtain ⟨n, hn1, hn2⟩ :=
    ((hφ.tendsto_atTop.eventually hc).and (h3.eventually (gt_mem_nhds hc0))).exists
  exact absurd hn1 (not_le.mpr hn2)

