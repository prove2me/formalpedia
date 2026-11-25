-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.nfBasis_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:41:09.477867+00:00
-- url     : https://prove2.me/submissions/b5a2a15a-e8b3-4d4e-a204-c4f12afa612a

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
theorem _root_.solution (ϖ : kˣ) (g : GL n k) (e : Fin c → ℤ) (z : n → k) : (nfBasis ϖ g e z).val =
    fromBlocks g.val (Matrix.of fun r i => if i.val = 0 then z r * (ϖ : k) ^ e i else 0) 0
      (diagonal fun i => (ϖ : k) ^ e i) := by
  change fromBlocks 1 _ 0 1 * fromBlocks g.val 0 0 1 * fromBlocks 1 0 0 (diagonal _) = _
  rw [fromBlocks_multiply, fromBlocks_multiply]
  ext (r | r) (i | i) <;> simp
end GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
