-- Prove2me | solution 1 for GlobalTheory.ClassParam.map_smul_tensor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:24.005794+00:00
-- url     : https://prove2.me/submissions/e6918ca3-e99b-4fe4-a1f8-187564b432f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
import Theorems.Thm_GlobalTheory_ClassParam_algebraMap_tmul

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
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion
attribute [local instance] algLk
variable {F E : Type} [Field F] [Field E] [Algebra F E] {c : E ≃ₐ[F] E} {r : ℕ} {P : E[X]}
  (k : Type) [Field k] [Algebra F k]
namespace GlobalTheory.ClassParam
theorem _root_.solution (f : AdjoinRoot P →ₗ[E] E) (a : E ⊗[F] k) (y : AdjoinRoot P ⊗[F] k) :
    TensorProduct.map (f.restrictScalars F) LinearMap.id (a • y)
      = a * TensorProduct.map (f.restrictScalars F) LinearMap.id y := by
  rw [Algebra.smul_def]
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add a a' h h' => rw [map_add, add_mul, map_add, h, h', add_mul]
  | tmul e t =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' h h' => rw [mul_add, map_add, h, h', map_add, mul_add]
    | tmul l s =>
      have : AdjoinRoot.of P e * l = e • l := (Algebra.smul_def e l).symm
      simp [algebraMap_tmul, this]
end GlobalTheory.ClassParam
