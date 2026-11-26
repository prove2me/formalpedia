-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41AllLevelsOccupationV16
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:13:28.284204+00:00
-- url     : https://prove2.me/submissions/211683df-416b-4922-963f-596afa4d8065

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41JointDenseSlopeV16
import Theorems.Thm_Kyprianou_Ch04_exercise41RealSlopeOccupationV16
import Theorems.Thm_Kyprianou_Ch04_exercise41RealGermFromNNRealV16
import Theorems.Thm_Kyprianou_Ch04_exercise41DenseSlopeExtendV12
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
open Kyprianou.Ch04
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal inferInstance) (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) :
    ∀ᵐ w ∂P, ∀ b : ℝ, volume {s : ℝ | 0 ≤ s ∧ L.X s.toNNReal w = b} = 0 := by
  let q := TopologicalSpace.denseSeq NNReal
  have hq : DenseRange q := TopologicalSpace.denseRange_denseSeq NNReal
  filter_upwards [exercise41JointDenseSlopeV16 P F L hBV hd q] with w hw
  apply exercise41RealSlopeOccupationV16 (fun s => L.X s.toNNReal w)
  filter_upwards [hw] with s hs hs0
  obtain ⟨n,hn⟩ := hs
  let e : NNReal := 1 / ((n : NNReal) + 1)
  have hr (u : NNReal) : ContinuousWithinAt
      (fun v => L.X (s.toNNReal + v) w - L.X s.toNNReal w) (Ici u) u := by
    apply ContinuousWithinAt.sub _ continuousWithinAt_const
    apply (L.rightCont w (s.toNNReal + u)).comp
    · exact continuousWithinAt_const.add continuousWithinAt_id
    · intro v hv
      change s.toNNReal + u ≤ s.toNNReal + v
      exact add_le_add_right (show u ≤ v from hv) s.toNNReal
  have H := exercise41DenseSlopeExtendV12
    (fun v => L.X (s.toNNReal + v) w - L.X s.toNNReal w) q hq hr (L.drift / 2) e hn
  apply exercise41RealGermFromNNRealV16 (fun v => L.X v w) s hs0 e (by dsimp [e]; positivity)
  intro u hu hlt
  exact lt_of_lt_of_le (mul_pos (by linarith) (by exact_mod_cast hu)) (H u hu hlt)
