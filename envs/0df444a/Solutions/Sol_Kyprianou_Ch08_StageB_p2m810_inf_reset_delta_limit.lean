-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_inf_reset_delta_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:10:05.271262+00:00
-- url     : https://prove2.me/submissions/e782ad5b-77cb-4cd8-a38c-66ca32729f15


import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Source-faithful reflected exit proof. -/
theorem solution : ∀ (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
      HasSourceScaleFamily ψ W →
      ∀ q : ℝ, 0 ≤ q → (∀ b : ℝ, 0 < b → 0 < W q b) →
      Tendsto (fun ε : ℝ => (Zscale q (W q) ε - 1) / W q ε)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  intro ψ W hW q hq hp
  have hw := hW q hq
  have hnn := hw.2.2.1
  have hc := hw.2.2.2.1
  have hm := hw.2.2.2.2.1
  have hpos : ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0), 0 < ε := self_mem_nhdsWithin
  have hb : ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
      0 ≤ (Zscale q (W q) ε - 1) / W q ε ∧
      (Zscale q (W q) ε - 1) / W q ε ≤ q*ε := by
    filter_upwards [hpos] with ε he
    have hwi : IntervalIntegrable (W q) volume 0 ε :=
      (hc.mono (by rw [uIcc_of_le he.le]; exact Icc_subset_Ici_self)).intervalIntegrable
    have hi0 : 0 ≤ ∫ y in (0 : ℝ)..ε, W q y :=
      intervalIntegral.integral_nonneg he.le (fun y _ => hnn y)
    have hi : (∫ y in (0 : ℝ)..ε, W q y) ≤ ε * W q ε := by
      calc
        _ ≤ ∫ _ : ℝ in (0 : ℝ)..ε, W q ε :=
          intervalIntegral.integral_mono_on he.le hwi
            (continuous_const.intervalIntegrable 0 ε)
            (fun y hy => hm hy.1 he.le hy.2)
        _ = _ := by simp [intervalIntegral.integral_const]
    unfold Zscale
    have hε := hp ε he
    constructor
    · apply div_nonneg _ hε.le
      linarith [mul_nonneg hq hi0]
    · apply (div_le_iff₀ hε).2
      nlinarith [mul_le_mul_of_nonneg_left hi hq]
  have ht : Tendsto (fun ε : ℝ => q*ε) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using (tendsto_const_nhds (x := q)).mul
      (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun ε : ℝ => ε)
        (nhdsWithin 0 (Ioi 0)) (nhds 0))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (hb.mono fun _ h => h.1) (hb.mono fun _ h => h.2)
