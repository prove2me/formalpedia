-- Prove2me | solution 1 for NonsmoothNewton.Shared.exists_local_bJac_control
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-29T20:15:45.171447+00:00
-- url     : https://prove2.me/submissions/5f1e551a-2d2e-48d7-a902-dbe73430d378

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
open Filter Topology Set
open NonsmoothNewton.Shared
theorem solution
    {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (F : E → G) (hF : LocallyLipschitz F) (x : E) :
    ∃ K : NNReal, ∃ r : ℝ, 0 < r ∧
      LipschitzOnWith K F (Metric.closedBall x r) ∧
      (∀ y ∈ Metric.ball x r, (bJac F y).Nonempty) ∧
      (∀ y ∈ Metric.ball x r,
        ∀ V ∈ bJac F y, ‖V‖ ≤ (K : ℝ)) := by
  rcases hF x with ⟨K, s, hs, hLip⟩
  rcases Metric.mem_nhds_iff.mp hs with ⟨ρ, hρ, hρs⟩
  let r : ℝ := ρ / 2
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hrρ : r < ρ := by
    dsimp [r]
    linarith
  have hsub : Metric.closedBall x r ⊆ s :=
    (Metric.closedBall_subset_ball hrρ).trans hρs
  have hLip' : LipschitzOnWith K F (Metric.closedBall x r) :=
    hLip.mono hsub
  refine ⟨K, r, hr, hLip', ?_, ?_⟩
  · intro y hy
    have hNhd : Metric.closedBall x r ∈ 𝓝 y :=
      Metric.closedBall_mem_nhds_of_mem hy
    rcases Metric.mem_nhds_iff.mp hNhd with ⟨η, hη, hηsub⟩
    let _ : MeasurableSpace E := borel E
    have _ : BorelSpace E := ⟨rfl⟩
    let w := Module.Basis.ofVectorSpace ℝ E
    have hAE :
        ∀ᵐ z ∂w.addHaar,
          z ∈ Metric.closedBall x r →
            DifferentiableWithinAt ℝ F (Metric.closedBall x r) z :=
      hLip'.ae_differentiableWithinAt_of_mem
    have hDense :
        Dense {z : E | z ∈ Metric.closedBall x r →
          DifferentiableWithinAt ℝ F (Metric.closedBall x r) z} :=
      MeasureTheory.Measure.dense_of_ae hAE
    have hyCl :
        y ∈ closure {z : E |
          z ∈ Metric.ball y η ∧ DifferentiableAt ℝ F z} := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      have hm : 0 < min ε η := lt_min hε hη
      rcases Metric.dense_iff.mp hDense y (min ε η) hm with
        ⟨z, hzBall, hzPred⟩
      have hzη : z ∈ Metric.ball y η :=
        Metric.ball_subset_ball (min_le_right _ _) hzBall
      have hzε : z ∈ Metric.ball y ε :=
        Metric.ball_subset_ball (min_le_left _ _) hzBall
      have hzs : z ∈ Metric.closedBall x r := hηsub hzη
      have hsn : Metric.closedBall x r ∈ 𝓝 z :=
        mem_of_superset (Metric.isOpen_ball.mem_nhds hzη) hηsub
      have hzd : DifferentiableAt ℝ F z :=
        (hzPred hzs).differentiableAt hsn
      exact ⟨z, ⟨hzη, hzd⟩, Metric.mem_ball'.mp hzε⟩
    rcases mem_closure_iff_seq_limit.mp hyCl with ⟨u, hu, huT⟩
    have huNhd : ∀ k, Metric.closedBall x r ∈ 𝓝 (u k) := fun k =>
      mem_of_superset (Metric.isOpen_ball.mem_nhds (hu k).1) hηsub
    have hDball :
        ∀ k, fderiv ℝ F (u k) ∈ Metric.closedBall 0 (K : ℝ) := by
      intro k
      rw [mem_closedBall_zero_iff]
      exact (hu k).2.hasFDerivAt.le_of_lipschitzOn (huNhd k) hLip'
    rcases tendsto_subseq_of_bounded Metric.isBounded_closedBall hDball with
      ⟨V, _, φ, hφ, hVT⟩
    refine ⟨V, u ∘ φ, huT.comp (StrictMono.tendsto_atTop hφ), ?_, ?_⟩
    · intro k
      exact (hu (φ k)).2
    · simpa [Function.comp_def] using hVT
  · intro y hy V hV
    rcases hV with ⟨u, huT, huD, hDu⟩
    have huBall : ∀ᶠ k in atTop, u k ∈ Metric.ball x r :=
      huT.eventually (Metric.isOpen_ball.mem_nhds hy)
    have hDBall :
        ∀ᶠ k in atTop,
          fderiv ℝ F (u k) ∈ Metric.closedBall 0 (K : ℝ) := by
      filter_upwards [huBall] with k hk
      rw [mem_closedBall_zero_iff]
      exact (huD k).hasFDerivAt.le_of_lipschitzOn
        (Metric.closedBall_mem_nhds_of_mem hk) hLip'
    exact mem_closedBall_zero_iff.mp
      (Metric.isClosed_closedBall.mem_of_tendsto hDu hDBall)
