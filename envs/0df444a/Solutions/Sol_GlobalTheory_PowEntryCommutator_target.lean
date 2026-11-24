-- Prove2me | solution 1 for GlobalTheory.PowEntryCommutator.target
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:42:31.819009+00:00
-- url     : https://prove2.me/submissions/323df5cc-1548-4e0f-8ffd-adb77c055367

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PowEntryCommutator
import Theorems.Thm_GlobalTheory_PowEntryCommutator_pow_entry_commutator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PowEntryCommutator
open Matrix
namespace GlobalTheory.PowEntryCommutator
theorem _root_.solution : ∀ {A : Type} [inst : Ring A] {n : ℕ} (E : Fin n → Fin n → A), Formalism.REAL.GlRel E →
    ∀ (a b : Fin n) (m : ℕ) (c e : Fin n),
    E a b * ((Matrix.of : (Fin n → Fin n → A) → Matrix (Fin n) (Fin n) A) E ^ m) c e -
      ((Matrix.of : (Fin n → Fin n → A) → Matrix (Fin n) (Fin n) A) E ^ m) c e * E a b =
    (if b = c then ((Matrix.of : (Fin n → Fin n → A) → Matrix (Fin n) (Fin n) A) E ^ m) a e
      else (0 : A)) -
    if e = a then ((Matrix.of : (Fin n → Fin n → A) → Matrix (Fin n) (Fin n) A) E ^ m) c b
      else (0 : A) :=
  fun E hE a b m c e => pow_entry_commutator E hE a b m c e
end GlobalTheory.PowEntryCommutator
