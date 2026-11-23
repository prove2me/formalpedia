-- Prove2me | solution 1 for GlobalTheory.ClassParam.HidaSetting.traceForm_bij
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:57.897101+00:00
-- url     : https://prove2.me/submissions/0b6f7b57-fcf7-47c6-bb54-806ba81de72f

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
theorem _root_.solution (S : HidaSetting σ τ α b) :
    Function.Bijective (Algebra.traceForm A B) := by
  have h : IsUnit (LinearMap.toMatrix b b.dualBasis (Algebra.traceForm A B)).det := by
    have : LinearMap.toMatrix b b.dualBasis (Algebra.traceForm A B)
        = (Algebra.traceMatrix A b)ᵀ := by
      ext i j
      simp [LinearMap.toMatrix_apply, Algebra.traceMatrix_apply]
    rw [this, Matrix.det_transpose]; exact S.perf
  have := (LinearEquiv.ofIsUnitDet h).bijective
  rwa [← LinearEquiv.coe_coe, LinearEquiv.coe_ofIsUnitDet] at this
end HidaSetting
end GlobalTheory.ClassParam
