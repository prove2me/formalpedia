-- Prove2me | solution 1 for GroundTheory.Automorphic.map_det_krylov_C_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:07:59.479889+00:00
-- url     : https://prove2.me/submissions/0b779eb4-5eba-44ec-8687-d7f8bdd35f5e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjCyclic
import Theorems.Thm_GroundTheory_Automorphic_map_krylov

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
variable {E : Type*} [Field E]
namespace GroundTheory.Automorphic
theorem _root_.solution {T : Type*} [CommRing T] (M : Matrix (Fin n) (Fin n) E)
    (ψ : MvPolynomial (Fin n) E →+* T) :
    ψ (krylov (M.map MvPolynomial.C) (fun i => MvPolynomial.X i)).det =
      (krylov ((M.map MvPolynomial.C).map ψ) (ψ ∘ fun i => MvPolynomial.X i)).det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, map_krylov]
end GroundTheory.Automorphic
