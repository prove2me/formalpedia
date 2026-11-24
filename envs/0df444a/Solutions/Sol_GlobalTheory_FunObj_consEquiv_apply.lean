-- Prove2me | solution 1 for GlobalTheory.FunObj.consEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:38:08.458807+00:00
-- url     : https://prove2.me/submissions/e408b115-2810-4c3c-967b-52732d135664

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlatTensorPureTensorEqProdContr

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
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.LocFlat
namespace GlobalTheory.FunObj
theorem _root_.solution {n : ℕ} (E : Fin (n + 1) → Type) [∀ j, MeasurableSpace (E j)]
    (p : E 0 × ∀ j : Fin n, E j.succ) : consEquiv E p = Fin.cons p.1 p.2 :=
  (Fin.insertNth_zero p.1 p.2).trans rfl
end GlobalTheory.FunObj
