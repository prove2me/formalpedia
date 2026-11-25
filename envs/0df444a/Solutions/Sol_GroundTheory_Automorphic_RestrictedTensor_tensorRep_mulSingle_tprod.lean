-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.tensorRep_mulSingle_tprod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:19:05.381182+00:00
-- url     : https://prove2.me/submissions/ca692501-25a9-4642-9617-ebdc11a9054a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Restricted
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TotallyDisconnectedSpaceRestrictedProduct
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Smooth

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
variable {ι : Type*} {G : ι → Type*} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  [∀ v, IsTopologicalGroup (G v)] [∀ v, LocallyCompactSpace (G v)] [∀ v, T2Space (G v)]
  [∀ v, TotallyDisconnectedSpace (G v)]
  {K : ∀ v, Subgroup (G v)} [hKo : Fact (∀ v, IsOpen (K v : Set (G v)))]
  [hKc : ∀ v, CompactSpace (K v)]
  {V : ι → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
  {π : ∀ v, Representation ℂ (G v) (V v)} {ξ : ∀ v, V v}
omit [∀ v, TopologicalSpace (G v)] [∀ v, IsTopologicalGroup (G v)]
  [∀ v, LocallyCompactSpace (G v)] [∀ v, T2Space (G v)] [∀ v, TotallyDisconnectedSpace (G v)]
  hKo hKc
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution [DecidableEq ι] (a : ι) (k : G a) (x : ∀ v, V v) :
    tensorRep K π (RestrictedProduct.mulSingle K a k) (tprod ℂ x) =
      tprod ℂ (Function.update x a (π a k (x a))) := by
  rw [tensorRep_tprod]
  congr 1
  funext v
  by_cases hv : v = a
  · subst hv
    simp
  · rw [Function.update_of_ne hv, RestrictedProduct.coe_mulSingle_apply,
      Pi.mulSingle_eq_of_ne hv, map_one, Module.End.one_apply]
end GroundTheory.Automorphic.RestrictedTensor
