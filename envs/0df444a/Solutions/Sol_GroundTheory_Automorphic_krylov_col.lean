-- Prove2me | solution 1 for GroundTheory.Automorphic.krylov_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:02:57.236935+00:00
-- url     : https://prove2.me/submissions/ac59a4cc-66e5-4997-9752-9876f34c62c3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjCyclic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Polynomial Module Matrix
variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
namespace GroundTheory.Automorphic
theorem _root_.solution (M : Matrix (Fin n) (Fin n) R) (v : Fin n → R) (k : Fin n) :
    (krylov M v).col k = M ^ (k : ℕ) *ᵥ v := rfl
end GroundTheory.Automorphic
