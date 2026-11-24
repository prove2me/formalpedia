-- Prove2me | solution 1 for GlobalTheory.multilinear_vanish_of_prod_vanish
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:29:51.298136+00:00
-- url     : https://prove2.me/submissions/051535ce-62c4-421c-83b5-36668693c219

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MultilinearVanishOfProdVanish
import Theorems.Thm_GlobalTheory_multilinear_vanish_of_prod_vanish_of_agree_off_finset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Function
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] {X : ι → Type} (A : ∀ i, Submodule K (X i → K)) {M : Type} [AddCommGroup M]
    [Module K M] (P : MultilinearMap K (fun i => A i) M) {D : Type} (s : Finset D) (c : D → K)
    (f : D → ∀ i, A i)
    (hx : ∀ x : ∀ i, X i, ∑ d ∈ s, c d * ∏ i, (f d i : X i → K) (x i) = 0) :
    ∑ d ∈ s, c d • P (f d) = 0 :=
  multilinear_vanish_of_prod_vanish_of_agree_off_finset A P univ s c f (fun i hi => absurd (mem_univ i) hi) hx
end GlobalTheory
