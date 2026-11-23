-- Prove2me | solution 1 for GlobalTheory.ClassParam.HidaSetting.trace_star
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:57.868181+00:00
-- url     : https://prove2.me/submissions/04004a14-0a3f-4829-bb93-8acdd88e7243

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer

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
theorem _root_.solution (S : HidaSetting σ τ α b) (z : B) :
    Algebra.trace A B (τ z) = σ (Algebra.trace A B z) := by
  have := Algebra.trace_eq_of_equiv_equiv
    (RingEquiv.ofRingHom σ σ (RingHom.ext S.hσ) (RingHom.ext S.hσ))
    (RingEquiv.ofRingHom τ τ (RingHom.ext S.hτ) (RingHom.ext S.hτ))
    (RingHom.ext fun a => (S.comp a).symm) z
  rw [this]
  exact (S.hσ _).symm
end HidaSetting
end GlobalTheory.ClassParam
