-- Prove2me | solution 1 for GlobalTheory.IntertwinerCoprimeCharpoly.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:43:53.998362+00:00
-- url     : https://prove2.me/submissions/235b8f0a-789e-457e-8e38-364018c11ed9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfIntertwineOfIsCoprimeCharpoly
import Theorems.Thm_GlobalTheory_IntertwinerCoprimeCharpoly_eq_zero_of_intertwine_of_isCoprime_charpoly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntertwinerCoprimeCharpoly
open Polynomial
namespace GlobalTheory.IntertwinerCoprimeCharpoly
theorem _root_.solution : ∀ {K : Type} [inst : Field K] {a b : ℕ} (A : Matrix (Fin a) (Fin a) K)
    (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K),
    IsCoprime (Matrix.charpoly A) (Matrix.charpoly B) → C * A = B * C →
      C = (0 : Matrix (Fin b) (Fin a) K) :=
  fun A B C hcop h => eq_zero_of_intertwine_of_isCoprime_charpoly A B C hcop h
end GlobalTheory.IntertwinerCoprimeCharpoly
