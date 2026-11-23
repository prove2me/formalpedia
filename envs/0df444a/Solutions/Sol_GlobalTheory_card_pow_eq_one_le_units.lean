-- Prove2me | solution 1 for GlobalTheory.card_pow_eq_one_le_units
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:01.581555+00:00
-- url     : https://prove2.me/submissions/f3b780ae-0eae-43d2-b60b-4c0a27ff4f44

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardPowEqOneLeOfIsCyclicUnits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {M : Type*} [Monoid M] [Finite M] {d : ℕ} (hd : 0 < d) :
    Nat.card {x : M // x ^ d = 1} ≤ Nat.card {x : Mˣ // x ^ d = 1} := by
  refine Nat.card_le_card_of_injective
    (fun x => ⟨Units.ofPowEqOne x.1 d x.2 hd.ne', Units.pow_ofPowEqOne _ _⟩) ?_
  intro x y hxy
  apply Subtype.ext
  have := congrArg (fun z : {u : Mˣ // u ^ d = 1} => ((z.1 : Mˣ) : M)) hxy
  simpa using this
end GlobalTheory
