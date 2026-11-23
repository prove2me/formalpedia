-- Prove2me | solution 1 for GlobalTheory.ClassParam.HidaSetting.eq_of_trace
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:21.571497+00:00
-- url     : https://prove2.me/submissions/2a70fd1b-cd3c-47f0-9588-4e5315a224e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
import Theorems.Thm_GlobalTheory_ClassParam_HidaSetting_traceForm_bij

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
variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {r : ℕ}
variable {σ : A →+* A} {τ : B →+* B} {α : B} {b : Module.Basis (Fin r) A B}
  {J : Matrix (Fin r) (Fin r) A}
namespace GlobalTheory.ClassParam
namespace HidaSetting
theorem _root_.solution (S : HidaSetting σ τ α b) {x x' : B}
    (h : ∀ y, Algebra.trace A B (x * y) = Algebra.trace A B (x' * y)) : x = x' :=
  S.traceForm_bij.1 (LinearMap.ext h)
end HidaSetting
end GlobalTheory.ClassParam
