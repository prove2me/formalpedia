-- Prove2me | solution 1 for GlobalTheory.FunObj.ch_add_keptPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:48:22.52784+00:00
-- url     : https://prove2.me/submissions/ffe3416b-37f4-416f-a949-ecb84305dcf4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable {k : Type*} [Field k] {n : Type*} {c : ℕ} {n' : Type*}
namespace GlobalTheory.FunObj
theorem _root_.solution (z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (w : KeptVar n c n' → k) :
    ch (z + keptPt w) = ch z := by
  simp [ch, keptPt, Kept]
end GlobalTheory.FunObj
