-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.nfBasis_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:41:17.511623+00:00
-- url     : https://prove2.me/submissions/602387b1-412d-41f1-b5c9-ca88bd293cf3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
theorem _root_.solution (ϖ : kˣ) (e : Fin c → ℤ) (z : n → k) : nfBasis ϖ 1 e z = normalBasis ϖ e z := by
  simp [nfBasis, normalBasis]
end GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
