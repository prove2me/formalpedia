-- Prove2me | solution 1 for GlobalTheory.JR.WeilQuad.Fnf.continuous_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:14:20.658879+00:00
-- url     : https://prove2.me/submissions/23a71717-5746-4028-aa5e-f3218100a124

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFOpNOpFOpGauss

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilQuad GlobalTheory.JR.WeilQuad.Fnf
namespace GlobalTheory.JR.WeilQuad.Fnf
theorem _root_.solution {F : Type} [NormedField F] (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) : Continuous ψ := by
  rw [continuous_iff_continuousAt]
  intro a
  refine (continuousAt_const (y := ψ a)).congr ?_
  filter_upwards [Metric.ball_mem_nhds a one_pos] with y hy
  show ψ a = ψ y
  have h1 : ψ (y - a) = 1 := hψ.1 _ (by rw [← dist_eq_norm]; exact (Metric.mem_ball.1 hy).le)
  calc ψ a = ψ a * ψ (y - a) := by rw [h1, mul_one]
    _ = ψ y := by rw [← AddChar.map_add_eq_mul]; congr 1; abel
end GlobalTheory.JR.WeilQuad.Fnf
