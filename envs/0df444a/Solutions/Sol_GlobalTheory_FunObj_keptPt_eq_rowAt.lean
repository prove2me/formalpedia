-- Prove2me | solution 1 for GlobalTheory.FunObj.keptPt_eq_rowAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:39:02.24582+00:00
-- url     : https://prove2.me/submissions/597b95a7-2f3a-4f4e-a662-3d99f9890b99

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
theorem _root_.solution (hc : Odd c) (w : KeptVar n c n' → k) :
    keptPt w = rowAt n c (c / 2 + 1) fun s => w (rowIx hc s) := by
  classical
  ext (r | l) (s | i)
  · simp [keptPt, rowAt, Kept]
  · simp [keptPt, rowAt, Kept, Nat.not_even_iff_odd.2 hc]
  · by_cases hl : l.val = c / 2
    · obtain ⟨l, hl'⟩ := l
      obtain rfl : l = c / 2 := hl
      simp [keptPt, rowAt, Kept, hc, rowIx]
    · simp [keptPt, rowAt, Kept, hl]
  · simp [keptPt, rowAt, Kept]
end GlobalTheory.FunObj
