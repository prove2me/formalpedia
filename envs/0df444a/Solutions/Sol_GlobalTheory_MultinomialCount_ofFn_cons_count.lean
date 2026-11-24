-- Prove2me | solution 1 for GlobalTheory.MultinomialCount.ofFn_cons_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:00:42.927797+00:00
-- url     : https://prove2.me/submissions/05cf7b78-6b82-4be9-b70b-901048aa5dc0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardMultisetWordsMulFactorial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Classical
open GlobalTheory GlobalTheory.MultinomialCount
namespace GlobalTheory.MultinomialCount
theorem _root_.solution {I : Type} {k : ℕ} (a : I) (t : Fin k → I) (i : I) :
    (List.ofFn (Fin.cons a t : Fin (k+1) → I)).count i = (List.ofFn t).count i + if a = i then 1 else 0 := by
  rw [List.ofFn_succ]
  simp [List.count_cons, Fin.cons_zero, Fin.cons_succ]
end GlobalTheory.MultinomialCount
