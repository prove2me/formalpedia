-- Prove2me | solution 1 for GlobalTheory.KZ.Betti.polySlash_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:57:04.63857+00:00
-- url     : https://prove2.me/submissions/33d52a59-664f-441d-bc56-1bf3becd2f16

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
theorem _root_.solution (p : MvPolynomial (Fin 2) R) : slP 1 p = p := by
  have h1 : slP (R := R) 1 = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [slP_X]
    fin_cases i <;> simp [Matrix.one_apply]
  rw [h1, AlgHom.id_apply]
end GlobalTheory.KZ.Betti
