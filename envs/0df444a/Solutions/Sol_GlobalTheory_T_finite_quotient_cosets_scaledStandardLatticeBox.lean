-- Prove2me | solution 1 for GlobalTheory.T.finite_quotient_cosets_scaledStandardLatticeBox
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:22:10.852412+00:00
-- url     : https://prove2.me/submissions/2db0ac19-6495-4060-9db3-c78263eea84c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FiniteQuotientCosetsScaledStandardLatticeBox
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FiniteQuotientCosetsScaledStandardLatticeBoxStatement
import Theorems.Thm_GlobalTheory_BoxCosets_finite_cosets


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (c₁ c₂ : kˣ), {yb : (n → k) ⧸ box n c₂ | ∃ y ∈ box n c₁, Submodule.Quotient.mk y = yb}.Finite := by
  first | exact @GlobalTheory.BoxCosets.finite_cosets | exact GlobalTheory.BoxCosets.finite_cosets | (intros; apply GlobalTheory.BoxCosets.finite_cosets <;> assumption)
end _root_.GlobalTheory.T
