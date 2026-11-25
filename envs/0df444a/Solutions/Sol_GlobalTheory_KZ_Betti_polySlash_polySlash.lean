-- Prove2me | solution 1 for GlobalTheory.KZ.Betti.polySlash_polySlash
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:57:07.104799+00:00
-- url     : https://prove2.me/submissions/739512ca-72e2-4c78-b8fa-b57245753af8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_Letter
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_OpLDOneSubMemTriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped MatrixGroups TensorProduct
open Matrix
open GlobalTheory GlobalTheory.KZ
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}
open GlobalTheory.KZ.Betti
variable {R : Type} [CommRing R]
namespace GlobalTheory.KZ.Betti
theorem _root_.solution (m m' : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R) :
    slP m' (slP m p) = slP (m * m') p := by
  have h1 : (slP m').comp (slP m) = slP (R := R) (m * m') := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, slP_X, map_add, map_smul, Matrix.mul_apply, Fin.sum_univ_two,
      Int.cast_add, Int.cast_mul]
    module
  exact DFunLike.congr_fun h1 p
end GlobalTheory.KZ.Betti
