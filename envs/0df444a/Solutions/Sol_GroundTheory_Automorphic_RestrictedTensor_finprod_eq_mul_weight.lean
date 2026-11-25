-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.finprod_eq_mul_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:59:32.094202+00:00
-- url     : https://prove2.me/submissions/16bdab10-3138-4ef2-bece-2dd0795897a7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Restricted

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
theorem _root_.solution {ξ x : ∀ v, V v} (hx : IsRestricted ξ x) {l : ∀ v, Dual ℂ (V v)}
    (hl : ∀ᶠ v in cofinite, l v (ξ v) = 1) (v : ι) :
    ∏ᶠ w, l w (x w) = l v (x v) * ∏ᶠ w, weight {v} l x w := by
  classical
  have h0 : (fun w => l w (x w)) = weight ∅ l x := by
    funext w; rw [weight_of_notMem l x (Finset.notMem_empty w)]
  have h1 : weight {v} l x = Function.update (weight ∅ l x) v 1 := by
    funext w
    by_cases hw : w = v
    · subst hw; rw [Function.update_self, weight_of_mem l x (Finset.mem_singleton_self w)]
    · rw [Function.update_of_ne hw, weight_of_notMem l x (by simpa using hw),
        weight_of_notMem l x (Finset.notMem_empty w)]
  have h2 : weight ∅ l x = Function.update (weight ∅ l x) v (l v (x v)) := by
    have : weight ∅ l x v = l v (x v) := weight_of_notMem l x (Finset.notMem_empty v)
    rw [← this, Function.update_eq_self]
  rw [h0, h1]
  conv_lhs => rw [h2]
  exact finprod_update_eq_mul _ (finite_mulSupport_weight hx ∅ hl) v _
end GroundTheory.Automorphic.RestrictedTensor
