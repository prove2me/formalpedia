-- Prove2me | solution 1 for GlobalTheory.ClassParam.HidaSetting.det_gram_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:12:11.353632+00:00
-- url     : https://prove2.me/submissions/610cdcd2-0b96-4388-bcdc-440ae6e3ff8f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
import Theorems.Thm_GlobalTheory_ClassParam_HidaSetting_trace_star

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
theorem _root_.solution (S : HidaSetting σ τ α b) {x : B} (hx : τ x = x)
    (e : Module.Basis (Fin r) A B) : σ (gram τ x e).det = (gram τ x e).det := by
  rw [RingHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext i j
  simp only [gram, tf, Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
    Matrix.of_apply, ← S.trace_star, map_mul, hx, S.hτ]
  congr 1; ring
end HidaSetting
end GlobalTheory.ClassParam
