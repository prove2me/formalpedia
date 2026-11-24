-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.continuous_gaussR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:54:52.811352+00:00
-- url     : https://prove2.me/submissions/62ac9943-a955-47d7-aa0b-e7888431be1c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoreR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuadraticBoxVolumeBound

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WeilSiegel GlobalTheory.CompanionTheory.WeilSiegel.Inf0 GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox
variable {P ι : Type}
namespace GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox
theorem _root_.solution [Fintype P] [Fintype ι] (Pm : P → Matrix ι ι ℝ) :
    Continuous (gaussR Pm) := by
  unfold gaussR
  exact Real.continuous_exp.comp (continuous_const.mul (continuous_finset_sum _ fun w _ =>
    Continuous.dotProduct (continuous_apply w)
      (Continuous.matrix_mulVec continuous_const (continuous_apply w))))
end GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox
