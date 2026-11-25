-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.map_update_id_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:13:59.939908+00:00
-- url     : https://prove2.me/submissions/e9f90901-bd75-453d-8e12-7dbdf48ba725

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Smooth
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Window
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Irreducible

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
open PiTensorProduct Filter Function Module Set Topology
open scoped TensorProduct RestrictedProduct
variable {ι : Type*} {V : ι → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
variable {G : ι → Type*} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  [∀ v, IsTopologicalGroup (G v)] [∀ v, LocallyCompactSpace (G v)] [∀ v, T2Space (G v)]
  [∀ v, TotallyDisconnectedSpace (G v)]
  {K : ∀ v, Subgroup (G v)} [hKo : Fact (∀ v, IsOpen (K v : Set (G v)))]
  [hKc : ∀ v, CompactSpace (K v)]
  {π : ∀ v, Representation ℂ (G v) (V v)} {ξ : ∀ v, V v}
omit [∀ v, Module ℂ (V v)]
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution {κ : Type*} [DecidableEq κ] {M : κ → Type*} [∀ j, AddCommGroup (M j)]
    [∀ j, Module ℂ (M j)] (i : κ) (a b : End ℂ (M i)) :
    PiTensorProduct.map (R := ℂ) (Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i (a * b)) =
      PiTensorProduct.map (Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i a) *
        PiTensorProduct.map (Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i b) := by
  rw [← PiTensorProduct.map_mul]
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj
    simp only [Function.update_self]
  · simp only [Function.update_of_ne hj]
    rfl
end GroundTheory.Automorphic.RestrictedTensor
