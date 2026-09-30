-- Prove2me | solution 1 for NonsmoothNewton.Shared.exists_local_bJac_subset_thickening
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-29T22:44:34.61698+00:00
-- url     : https://prove2.me/submissions/d381f52a-d5a6-42f6-b5e5-ed40e9777693

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Theorems.Thm_NonsmoothNewton_Shared_exists_local_bJac_control
import Theorems.Thm_NonsmoothNewton_Shared_bJac_mem_of_tendsto
open Filter Topology Set
open NonsmoothNewton.Shared
theorem solution {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (F : E → G) (hF : LocallyLipschitz F) (x : E)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y, dist y x < δ →
      bJac F y ⊆ Metric.thickening ε (bJac F x) := by
  rcases exists_local_bJac_control F hF x with
    ⟨K, r, hr, _, _, hbound⟩
  by_contra h
  push_neg at h
  let ρ : ℕ → ℝ :=
    fun n => min (r / 2) (1 / ((n : ℝ) + 1))
  have hρpos : ∀ n, 0 < ρ n := by
    intro n
    dsimp [ρ]
    exact lt_min (half_pos hr) (by positivity)
  have hpick : ∀ n, ∃ y,
      dist y x < ρ n ∧
      ∃ V, V ∈ bJac F y ∧
        V ∉ Metric.thickening ε (bJac F x) := by
    intro n
    rcases h (ρ n) (hρpos n) with ⟨y, hy, hsub⟩
    rcases Set.not_subset.mp hsub with ⟨V, hV, hVo⟩
    exact ⟨y, hy, V, hV, hVo⟩
  choose y hy V hV hVout using hpick
  have hyr : ∀ n, y n ∈ Metric.ball x r := by
    intro n
    have hρr : ρ n < r := by
      calc
        ρ n ≤ r / 2 := by
          dsimp [ρ]
          exact min_le_left _ _
        _ < r := half_lt_self hr
    exact (Metric.mem_ball.2 (by
      simpa [dist_comm] using (hy n).trans hρr))
  have hVball :
      ∀ n, V n ∈ Metric.closedBall (0 : E →L[ℝ] G) (K : ℝ) := by
    intro n
    rw [mem_closedBall_zero_iff]
    exact hbound (y n) (hyr n) (V n) (hV n)
  rcases tendsto_subseq_of_bounded
      (s := Metric.closedBall (0 : E →L[ℝ] G) (K : ℝ))
      Metric.isBounded_closedBall hVball with
    ⟨W, _, φ, hφ, hWt⟩
  have hone :
      Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hybound : ∀ n, dist (y n) x ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    exact (hy n).le.trans (by
      dsimp [ρ]
      exact min_le_right _ _)
  have hyT : Tendsto y atTop (𝓝 x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ => dist_nonneg) hybound hone
  have hWbase : W ∈ bJac F x := by
    apply bJac_mem_of_tendsto (xseq := y ∘ φ) (Vseq := V ∘ φ)
    · exact hyT.comp (StrictMono.tendsto_atTop hφ)
    · exact hWt
    · intro n
      exact hV (φ n)
  rcases Metric.tendsto_atTop.mp hWt ε hε with ⟨N, hN⟩
  have hin :
      V (φ N) ∈ Metric.thickening ε (bJac F x) :=
    Metric.mem_thickening_iff.mpr ⟨W, hWbase, hN N le_rfl⟩
  exact hVout (φ N) hin
