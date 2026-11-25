-- Prove2me | solution 1 for GlobalTheory.RootEx.PerIndex.col_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:40:29.291048+00:00
-- url     : https://prove2.me/submissions/0100bd11-e2e2-4377-b6ff-dc9e20460473

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RelIndexPerLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.PerIndex
variable {k : Type} [Field k] [ValuativeRel k] {n : Type}
namespace GlobalTheory.RootEx.PerIndex
theorem _root_.solution (n' : Type) {c : ℕ}
    (e f : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k) (i : Fin c) :
    UnfoldShape.col (n' := n') (e + f) i
      = UnfoldShape.col (n' := n') e i + UnfoldShape.col (n' := n') f i := by
  funext r
  simp only [UnfoldShape.col, Pi.add_apply]
  split_ifs <;> simp
end GlobalTheory.RootEx.PerIndex
