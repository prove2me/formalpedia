-- Prove2me | solution 1 for GlobalTheory.JR.LinDesc.Swap.continuous_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:08:41.628928+00:00
-- url     : https://prove2.me/submissions/c8884304-32de-422b-b913-69b22e08d8c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LinearDescentPartialFourierEqFourierDescent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LinDesc GlobalTheory.JR.LinDesc.Swap
namespace GlobalTheory.JR.LinDesc.Swap
theorem _root_.solution {F : Type} [NormedField F] (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) :
    Continuous ψ := by
  rw [continuous_iff_continuousAt]
  intro x
  refine ContinuousAt.congr (f := fun _ => ψ x) continuousAt_const ?_
  filter_upwards [Metric.ball_mem_nhds x one_pos] with y hy
  rw [Metric.mem_ball, dist_eq_norm] at hy
  have : y = x + (y - x) := by ring
  rw [this, AddChar.map_add_eq_mul, hψ.1 _ hy.le, mul_one]
end GlobalTheory.JR.LinDesc.Swap
