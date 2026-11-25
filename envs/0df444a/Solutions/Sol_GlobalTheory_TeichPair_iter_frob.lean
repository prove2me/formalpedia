-- Prove2me | solution 1 for GlobalTheory.TeichPair.iter_frob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:17:20.609585+00:00
-- url     : https://prove2.me/submissions/63cb2e4f-7824-40dd-b524-f0aa40095dee

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EqZeroOfGe
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Formalism.L2.FormalSeriesBounds
open GlobalTheory GlobalTheory.TeichPair
namespace GlobalTheory.TeichPair
theorem _root_.solution {k O : Type} [CommRing k] [CommRing O] {d : ℕ} {l : ℕ} (f : ZMod d → O →+* k)
    (hf : ∀ a x, f (a + 1) x = f a x ^ l) (a : ZMod d) (x : O) (n : ℕ) : f (a + n) x = f a x ^ l ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, ← add_assoc, hf, ih, ← pow_mul, pow_succ]
end GlobalTheory.TeichPair
