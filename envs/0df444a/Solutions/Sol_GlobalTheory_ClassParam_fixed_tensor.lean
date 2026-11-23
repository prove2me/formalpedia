-- Prove2me | solution 1 for GlobalTheory.ClassParam.fixed_tensor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:57.948102+00:00
-- url     : https://prove2.me/submissions/eef4a641-93eb-4786-b41e-6b23afa98dbe

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
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion
attribute [local instance] algLk
variable {F E : Type} [Field F] [Field E] [Algebra F E] {c : E ≃ₐ[F] E} {r : ℕ} {P : E[X]}
  (k : Type) [Field k] [Algebra F k]
namespace GlobalTheory.ClassParam
theorem _root_.solution {W V : Type} [AddCommGroup W] [AddCommGroup V] [Module F W] [Module F V]
    (i : W →ₗ[F] V) (s : V →ₗ[F] V) (h : ∀ v, s v = v ↔ ∃ w, i w = v) (z : V ⊗[F] k) :
    s.rTensor k z = z ↔ ∃ w, i.rTensor k w = z := by
  have he : Function.Exact i (s - LinearMap.id : V →ₗ[F] V) := fun v => by
    rw [LinearMap.sub_apply, sub_eq_zero]; exact h v
  have := Module.Flat.rTensor_exact k he z
  simpa [LinearMap.rTensor_sub, sub_eq_zero] using this
end GlobalTheory.ClassParam
