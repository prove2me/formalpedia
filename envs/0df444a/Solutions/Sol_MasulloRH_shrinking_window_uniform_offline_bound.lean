-- Prove2me | solution 1 for MasulloRH.shrinking_window_uniform_offline_bound
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T01:36:25.235681+00:00
-- url     : https://prove2.me/submissions/720019ee-c94a-42d4-83ec-df6bd20f3386

-- New supporting proof for the Masullo trace-window frontier.
import Mathlib
import Theorems.Thm_MasulloRH_trace_window_comparison
import Definitions.Def_MasulloRH_RationalTrace
open MasulloRH MeasureTheory Set Filter Topology
theorem solution (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ α : ℝ, 0 < α → α ≤ δ →
      ∀ w : ZetaZerosInTraceStrip (1/2) → ℂ, (∀ ρ, ‖w ρ‖ ≤ 1) →
      ‖∑' ρ : ZetaZerosInTraceStrip (1/2),
          if 0 < |ρ.val.re - 1/2| ∧ |ρ.val.re - 1/2| < α
          then w ρ * zetaTraceTerm φ (1/2) ρ else 0‖ < ε := by
  classical
  intro ε hε
  let Z := ZetaZerosInTraceStrip (1/2)
  let d (ρ : Z) : ℝ := |ρ.val.re - 1/2|
  let T : Z → ℂ := zetaTraceTerm φ (1/2)
  have hT : Summable T := (trace_window_comparison (1/2) φ hφ).2.2.1
  let B (a : ℝ) (ρ : Z) : ℝ := if 0 < d ρ ∧ d ρ < a then ‖T ρ‖ else 0
  have hb (a : ℝ) (ρ : Z) : ‖B a ρ‖ ≤ ‖T ρ‖ := by
    dsimp [B]
    split <;> simp
  have hlim : Tendsto (fun a : ℝ ↦ ∑' ρ : Z, B a ρ) (𝓝 0) (𝓝 0) := by
    have hz (ρ : Z) : Tendsto (fun a : ℝ ↦ B a ρ) (𝓝 0) (𝓝 0) := by
      apply Tendsto.congr' (f₁ := fun _ : ℝ ↦ (0 : ℝ)) _ tendsto_const_nhds
      by_cases hp : 0 < d ρ
      · filter_upwards [Iio_mem_nhds hp] with a ha
        change a < d ρ at ha
        simp [B, not_lt.mpr ha.le]
      · exact Filter.Eventually.of_forall fun a ↦ by simp [B, hp]
    simpa using (tendsto_tsum_of_dominated_convergence hT.norm hz
      (Filter.Eventually.of_forall hb))
  obtain ⟨r, hr, hrB⟩ := Metric.eventually_nhds_iff.mp (hlim.eventually (Iio_mem_nhds hε))
  refine ⟨r/2, by positivity, ?_⟩
  intro a ha har w hw
  let F (ρ : Z) : ℂ := if 0 < d ρ ∧ d ρ < a then w ρ * T ρ else 0
  have hF (ρ : Z) : ‖F ρ‖ ≤ B a ρ := by
    dsimp [F, B]
    split
    · rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hw ρ)
    · simp
  have bs : Summable (B a) := hT.norm.of_norm_bounded (hb a)
  change ‖∑' ρ : Z, F ρ‖ < ε
  exact (norm_tsum_le_tsum_norm ((bs.of_norm_bounded hF).norm)).trans_lt
    ((Summable.tsum_le_tsum hF (bs.of_norm_bounded hF).norm bs).trans_lt
      (hrB (by simpa [Real.dist_eq, abs_of_pos ha] using (show a < r by linarith))))
