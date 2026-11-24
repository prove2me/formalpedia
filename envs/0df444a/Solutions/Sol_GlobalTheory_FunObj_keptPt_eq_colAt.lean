-- Prove2me | solution 1 for GlobalTheory.FunObj.keptPt_eq_colAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:38:10.484042+00:00
-- url     : https://prove2.me/submissions/572c3f37-f363-4d02-b114-963edc5523f6

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
variable {k : Type} [Field k] {n n' : Type} {c : ℕ}
namespace GlobalTheory.FunObj
theorem _root_.solution (hc : Even c) (w : KeptVar n c n' → k) :
    keptPt w = colAt n' c (c / 2 + 1) fun r => w (colIx hc r) := by
  classical
  ext (r | l) (s | i)
  · simp [keptPt, colAt, Kept]
  · by_cases hi : i.val = c / 2
    · obtain ⟨i, hi'⟩ := i
      obtain rfl : i = c / 2 := hi
      simp [keptPt, colAt, Kept, hc, colIx]
    · simp [keptPt, colAt, Kept, hi]
  · simp [keptPt, colAt, Kept, Nat.not_odd_iff_even.2 hc]
  · simp [keptPt, colAt, Kept]
end GlobalTheory.FunObj
