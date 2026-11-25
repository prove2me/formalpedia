-- Prove2me | solution 1 for GlobalTheory.HodgeGramLocal.isOpen_polydisc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:54:29.039481+00:00
-- url     : https://prove2.me/submissions/eb4fc830-7690-4b0f-b41d-cc47dde1d902

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeMetricGramMatrixLocalHolomorphicImPart
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero



set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff ComplexConjugate
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
noncomputable section
open GlobalTheory GlobalTheory.HodgeGramLocal
variable {n a g : ℕ}
namespace GlobalTheory.HodgeGramLocal
theorem _root_.solution (n : ℕ) : IsOpen (polydisc n 1) := by
  rw [show polydisc n 1 = ⋂ k, {z : Fin n → ℂ | ‖z k‖ < 1} by ext; simp [polydisc]]
  exact isOpen_iInter_of_finite fun k =>
    isOpen_lt (continuous_norm.comp (continuous_apply k)) continuous_const
end GlobalTheory.HodgeGramLocal
