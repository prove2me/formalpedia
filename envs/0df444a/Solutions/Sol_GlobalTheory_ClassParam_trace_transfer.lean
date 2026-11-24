-- Prove2me | solution 1 for GlobalTheory.ClassParam.trace_transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:13:31.311783+00:00
-- url     : https://prove2.me/submissions/2e7b030a-ebc7-45f9-8c63-a55d11c0f46f

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
    Algebra.trace A B (ψ x) = f (Algebra.trace R S x) := by
  rw [Algebra.trace_eq_matrix_trace b', Algebra.trace_eq_matrix_trace b,
    leftMulMatrix_transfer f ψ h b b' hb, AddMonoidHom.map_trace]
end GlobalTheory.ClassParam
