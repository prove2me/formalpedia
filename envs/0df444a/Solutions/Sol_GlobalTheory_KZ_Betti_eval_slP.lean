-- Prove2me | solution 1 for GlobalTheory.KZ.Betti.eval_slP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:57:02.452187+00:00
-- url     : https://prove2.me/submissions/bf038f58-8c92-4fad-8f0f-8cf415a66d1c

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
theorem _root_.solution (m : Matrix (Fin 2) (Fin 2) ℤ) (u : Fin 2 → R) (p : MvPolynomial (Fin 2) R) :
    MvPolynomial.eval u (slP m p) = MvPolynomial.eval (m.map (Int.castRingHom R) *ᵥ u) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [slP]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, slP_X, MvPolynomial.eval_X, map_add, MvPolynomial.smul_eval]
    congr 1
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
end GlobalTheory.KZ.Betti
