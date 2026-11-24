-- Prove2me | solution 1 for GlobalTheory.ClassParam.norm_transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:13:27.620015+00:00
-- url     : https://prove2.me/submissions/791e724a-0b24-4158-9481-2c72586b03d4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
import Theorems.Thm_GlobalTheory_ClassParam_leftMulMatrix_transfer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial TensorProduct Matrix Formalism.UG
open GlobalTheory GlobalTheory.ClassParam
variable {R S A B : Type} [CommRing R] [CommRing S] [CommRing A] [CommRing B] [Algebra R S]
  [Algebra A B] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.ClassParam
theorem _root_.solution (f : R →+* A) (ψ : S →+* B)
    (h : ∀ a, ψ (algebraMap R S a) = algebraMap A B (f a)) (b : Module.Basis ι R S)
    (b' : Module.Basis ι A B) (hb : ∀ i, ψ (b i) = b' i) (x : S) :
    Algebra.norm A (ψ x) = f (Algebra.norm R x) := by
  rw [Algebra.norm_eq_matrix_det b', Algebra.norm_eq_matrix_det b,
    leftMulMatrix_transfer f ψ h b b' hb, RingHom.map_det]
  rfl
end GlobalTheory.ClassParam
