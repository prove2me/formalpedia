-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.boxR_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:54:45.635135+00:00
-- url     : https://prove2.me/submissions/a2363980-0407-4dbc-8801-d37d8da85d0a

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
theorem _root_.solution [Fintype P] [Fintype ι] :
    boxR (fun _ : P => (1 : ℝ)) = Metric.closedBall (0 : P → ι → ℝ) 1 := by
  ext x
  simp only [boxR, Set.mem_setOf_eq, mem_closedBall_zero_iff]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).symm
end GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox
