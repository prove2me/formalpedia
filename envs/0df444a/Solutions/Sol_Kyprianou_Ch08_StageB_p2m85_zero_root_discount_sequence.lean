-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m85_zero_root_discount_sequence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T19:20:59.3688+00:00
-- url     : https://prove2.me/submissions/44123a57-e192-4a0f-a919-a6d63dd5f82f

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_laplace_gap_pos
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open Kyprianou.Ch08 Kyprianou.Ch08.StageB ProbabilityTheory

theorem solution
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ) (hW : HasSourceScaleFamily ψ W)
    (hc : ConvexOn ℝ (Ici 0) ψ) (hz : ψ 0 = 0) (hφ : Phi ψ 0 = 0) :
    Tendsto (fun n : ℕ => ψ (1 / ((n : ℝ)+1))) atTop (nhdsWithin 0 (Ioi 0)) := by
  let s (n : ℕ) : ℝ := 1 / ((n : ℝ)+1)
  have hs (n : ℕ) : 0 < s n := by dsimp [s]; positivity
  have hp (n : ℕ) : 0 < ψ (s n) :=
    source_scale_laplace_gap_pos ψ W hW 0 (s n) le_rfl (hs n).le (by rw [hφ]; exact hs n)
  have hlimS : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hq : Tendsto (fun n => ψ (s n)) atTop (𝓝 0) := by
    have hu : Tendsto (fun n => s n * ψ 1) atTop (𝓝 0) := by
      simpa only [zero_mul] using hlimS.mul_const (ψ 1)
    apply squeeze_zero' (Eventually.of_forall fun n => (hp n).le) _ hu
    apply Eventually.of_forall
    intro n
    have hle : s n ≤ 1 := by dsimp [s]; apply (div_le_iff₀ (by positivity)).2; simp
    have h := hc.secant_mono (a := (0 : ℝ)) (x := s n) (y := 1)
      (by simp) (hs n).le (by norm_num) (hs n).ne' one_ne_zero hle
    simp only [hz, sub_zero, div_one] at h
    simpa only [mul_comm] using (div_le_iff₀ (hs n)).mp h
  exact tendsto_nhdsWithin_iff.mpr ⟨hq, Eventually.of_forall hp⟩
