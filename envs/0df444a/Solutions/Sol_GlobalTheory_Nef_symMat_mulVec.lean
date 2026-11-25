-- Prove2me | solution 1 for GlobalTheory.Nef.symMat_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:01:44.968619+00:00
-- url     : https://prove2.me/submissions/d71f781f-0fa0-4738-888b-a2565c5c35b5

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
theorem _root_.solution {R : Type} [CommRing R] (m : ℕ) (A : Matrix (Fin 2) (Fin 2) R)
    (p : Fin (m + 1) → R) :
    (symMat m A).mulVec p = fun a =>
      (∑ i : Fin (m + 1), C (p i) * (C (A 0 1) + C (A 1 1) * X) ^ (i : ℕ) * C (A 0 0) ^ (m - i)).coeff a := by
  funext a
  simp only [Matrix.mulVec, dotProduct, symMat, Matrix.of_apply, finset_sum_coeff]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc, coeff_C_mul, mul_comm]
end GlobalTheory.Nef
