-- Prove2me | solution 1 for GlobalTheory.ClassParam.mulUnit_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:13:26.52646+00:00
-- url     : https://prove2.me/submissions/df0e6bc4-91e6-49a8-aaf7-af03001117f9

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
theorem _root_.solution (z : Bˣ) (y : B) : (mulUnit A z).symm y = (z⁻¹ : Bˣ) * y := rfl
end GlobalTheory.ClassParam
