-- Prove2me | solution 1 for GroundTheory.Automorphic.map_krylov
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:03:01.777796+00:00
-- url     : https://prove2.me/submissions/2f6e59c2-2ac3-4165-bccc-8de8b29df75f

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
theorem _root_.solution (φ : R →+* S) (M : Matrix (Fin n) (Fin n) R) (v : Fin n → R) :
    (krylov M v).map φ = krylov (M.map φ) (φ ∘ v) := by
  ext i k
  simp only [krylov, Matrix.map_apply, Matrix.of_apply]
  rw [RingHom.map_mulVec]
  congr 2
  exact (map_pow φ.mapMatrix M k)
end GroundTheory.Automorphic
