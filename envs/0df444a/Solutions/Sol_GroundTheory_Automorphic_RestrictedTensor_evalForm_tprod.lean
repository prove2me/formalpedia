-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.evalForm_tprod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:03.853629+00:00
-- url     : https://prove2.me/submissions/eaba5571-1fcf-45f6-90b8-321409d25acb

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Restricted
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_restrictedLift_apply_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.RestrictedTensor
open PiTensorProduct Filter Function Module Set
open scoped TensorProduct RestrictedProduct
variable {ι : Type*} {V : ι → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
variable {N : Type*} [AddCommGroup N] [Module ℂ N]
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution {ξ : ∀ v, V v} {l : ∀ v, Dual ℂ (V v)}
    {hl : ∀ᶠ v in cofinite, l v (ξ v) = 1} {x : ∀ v, V v} (hx : IsRestricted ξ x) :
    evalForm ξ l hl (tprod ℂ x) = ∏ᶠ v, l v (x v) := by
  rw [evalForm, lift.tprod, restrictedLift_apply_of _ hx]
  simp only [MultilinearMap.constOfIsEmpty_apply, Function.const_apply, smul_eq_mul, mul_one]
  exact finprod_congr fun v => weight_of_notMem l x (Finset.notMem_empty v)
end GroundTheory.Automorphic.RestrictedTensor
