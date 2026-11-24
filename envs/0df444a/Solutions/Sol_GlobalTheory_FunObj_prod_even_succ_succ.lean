-- Prove2me | solution 1 for GlobalTheory.FunObj.prod_even_succ_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:37:57.813023+00:00
-- url     : https://prove2.me/submissions/48b19e32-2e32-408c-a630-4e56faa48df2

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
theorem _root_.solution (n : ℕ) (f : Fin (n + 2) → ℂ) : (∏ j : Fin (n + 2), if Even j.1 then f j else 1) =
    f 0 * ∏ j : Fin n, if Even j.1 then f j.succ.succ else 1 := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp [Nat.even_add_one]
end GlobalTheory.FunObj
