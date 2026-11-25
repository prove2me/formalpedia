-- Prove2me | solution 1 for GlobalTheory.Nef.symMat_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:01:43.999854+00:00
-- url     : https://prove2.me/submissions/c033f1f4-e74f-42cd-84c0-ad81117ce756

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TwistAtOfNe
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Polynomial
open GlobalTheory GlobalTheory.Nef
namespace GlobalTheory.Nef
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (m : ℕ)
    (A : Matrix (Fin 2) (Fin 2) R) : (symMat m A).map f = symMat m (A.map f) := by
  ext a i
  simp only [symMat, Matrix.map_apply, Matrix.of_apply]
  rw [← Polynomial.coeff_map]
  simp [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add]
end GlobalTheory.Nef
