-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41StoppedPositiveGermV12
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:10:08.482341+00:00
-- url     : https://prove2.me/submissions/21a44c5e-4e4b-4369-845d-839b8e9336f9

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41OriginSlopeAEV13
import Theorems.Thm_Kyprianou_Ch04_exercise41CountableSlopeTransferV13
import Theorems.Thm_Kyprianou_Ch04_exercise41DenseSlopeExtendV12
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
open Kyprianou.Ch04
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal inferInstance)
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift)
    (τ : Ω → NNReal)
    (hτ : ∀ s : NNReal, MeasurableSet[F.rightCont s] {w | τ w ≤ s}) :
    ∀ᵐ w ∂P, ∃ ε : NNReal, 0 < ε ∧
      ∀ u : NNReal, 0 < u → u < ε →
        0 < L.X (τ w + u) w - L.X (τ w) w := by
  let q := TopologicalSpace.denseSeq NNReal
  have hq : DenseRange q := TopologicalSpace.denseRange_denseSeq NNReal
  have h : ∀ᵐ w ∂P, ∃ n : ℕ, ∀ k : ℕ, 0 < q k →
      q k < 1 / ((n : NNReal) + 1) → L.drift / 2 * (q k : ℝ) ≤ L.X (q k) w := by
    filter_upwards [exercise41OriginSlopeAEV13 P F L hBV hd] with w hw
    obtain ⟨n,hn⟩ := hw
    exact ⟨n,fun k hk hk' => hn (q k) hk hk'.le⟩
  filter_upwards [exercise41CountableSlopeTransferV13 P F L τ hτ q (L.drift / 2) h] with w hw
  obtain ⟨n,hn⟩ := hw
  let e : NNReal := 1 / ((n : NNReal) + 1)
  have hr (u : NNReal) : ContinuousWithinAt
      (fun v => L.X (τ w + v) w - L.X (τ w) w) (Ici u) u := by
    apply ContinuousWithinAt.sub _ continuousWithinAt_const
    apply (L.rightCont w (τ w + u)).comp
    · exact continuousWithinAt_const.add continuousWithinAt_id
    · intro v hv
      change τ w + u ≤ τ w + v
      exact add_le_add_right (show u ≤ v from hv) (τ w)
  have hs := exercise41DenseSlopeExtendV12
    (fun v => L.X (τ w + v) w - L.X (τ w) w) q hq hr (L.drift / 2) e hn
  refine ⟨e,by dsimp [e]; positivity,?_⟩
  intro u hu hu'
  exact lt_of_lt_of_le (mul_pos (by linarith) (by exact_mod_cast hu)) (hs u hu hu')
