-- Prove2me | solution 1 for GroundTheory.Automorphic.exists_det_krylov_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:14:26.804564+00:00
-- url     : https://prove2.me/submissions/acf1b30b-88b8-4bfe-b5ef-9911728c7d24

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjCyclic
import Theorems.Thm_GroundTheory_Automorphic_map_det_krylov_C_X

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
variable [Infinite E]
namespace GroundTheory.Automorphic
theorem _root_.solution {L : Type*} [Field L] (φ : E →+* L)
    (M : Matrix (Fin n) (Fin n) E) (w : Fin n → L) (hw : (krylov (M.map φ) w).det ≠ 0) :
    ∃ v : Fin n → E, (krylov M v).det ≠ 0 := by
  classical
  set D : MvPolynomial (Fin n) E :=
    (krylov (M.map MvPolynomial.C) (fun i => MvPolynomial.X i)).det with hD
  have hD0 : D ≠ 0 := by
    intro h0
    have := map_det_krylov_C_X M (MvPolynomial.eval₂Hom φ w)
    rw [← hD] at this
    rw [h0, map_zero] at this
    apply hw
    rw [this]
    congr 2
    · ext i j; simp
    · ext i; simp
  by_contra hne
  push Not at hne
  apply hD0
  apply MvPolynomial.funext
  intro x
  rw [map_zero]
  have := map_det_krylov_C_X M (MvPolynomial.eval x)
  rw [← hD] at this
  rw [this]
  convert hne x using 3
  · ext i j; simp
  · ext i; simp
end GroundTheory.Automorphic
