-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail.measurableSet_boxR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:54:56.180515+00:00
-- url     : https://prove2.me/submissions/79bdec81-220a-4b5e-859d-122f47b0eec3

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoreR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuadraticBoxIntegralSmallBall

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology GlobalTheory.CompanionTheory.WeilSiegel.Inf0
open scoped ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WeilSiegel GlobalTheory.CompanionTheory.WeilSiegel.Inf0 GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail
variable {P ι : Type} [Fintype P] [Fintype ι]
namespace GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail
theorem _root_.solution (t : P → ℝ) : MeasurableSet (boxR t : Set (P → ι → ℝ)) := by
  have h : (boxR t : Set (P → ι → ℝ)) = ⋂ w, {x | ‖x w‖ ≤ t w} := by
    ext x; simp [boxR]
  rw [h]
  exact MeasurableSet.iInter fun w =>
    measurableSet_le (continuous_apply w).norm.measurable measurable_const
end GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail
