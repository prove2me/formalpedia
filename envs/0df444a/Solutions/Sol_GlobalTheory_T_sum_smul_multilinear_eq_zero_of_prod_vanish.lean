-- Prove2me | solution 1 for GlobalTheory.T.sum_smul_multilinear_eq_zero_of_prod_vanish
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:33:46.214369+00:00
-- url     : https://prove2.me/submissions/d05b0d85-ddc7-4d3c-91e0-c0824631a701

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MultilinearVanishOfProdVanish
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MultilinearVanishOfProdVanishStatement
import Theorems.Thm_GlobalTheory_multilinear_vanish_of_prod_vanish


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} (A : ∀ i, Submodule K (X i → K)) {M : Type} [AddCommGroup M] [Module K M] (P : MultilinearMap K (fun i => A i) M) {D : Type} (s : Finset D) (c : D → K) (f : D → ∀ i, A i), (∀ x : ∀ i, X i, ∑ d ∈ s, c d * ∏ i, (f d i : X i → K) (x i) = 0) → ∑ d ∈ s, c d • P (f d) = 0 := by
  first | exact @GlobalTheory.multilinear_vanish_of_prod_vanish | exact GlobalTheory.multilinear_vanish_of_prod_vanish | (intros; apply GlobalTheory.multilinear_vanish_of_prod_vanish <;> assumption)
end _root_.GlobalTheory.T
