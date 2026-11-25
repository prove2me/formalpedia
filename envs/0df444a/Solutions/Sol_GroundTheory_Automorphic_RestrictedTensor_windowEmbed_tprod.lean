-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.windowEmbed_tprod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:19:01.45937+00:00
-- url     : https://prove2.me/submissions/fe61bf74-6131-4bdc-bedb-0716273d0fe6

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Restricted
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TotallyDisconnectedSpaceRestrictedProduct
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Smooth
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_finiteEmbed_tprod


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
variable (hπ : ∀ v, IsAdmissible (π v)) (hξ : ∀ᶠ v in cofinite, ξ v ∈ fixedVectors (π v) (K v))
  {K' : ∀ v, Subgroup (G v)} (hK'c : ∀ v, IsCompact (K' v : Set (G v)))
  (hK'o : ∀ v, IsOpen (K' v : Set (G v)))
omit [∀ v, IsTopologicalGroup (G v)] [∀ v, LocallyCompactSpace (G v)] [∀ v, T2Space (G v)]
  [∀ v, TotallyDisconnectedSpace (G v)] hKo hKc
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution [DecidableEq ι] (S : Finset ι)
    (w : ∀ v : S, fixedVectors (π v) (K' v)) :
    windowEmbed ξ S (tprod ℂ w) = tprod ℂ (extend ξ S fun v => (w v : V v)) := by
  rw [windowEmbed, LinearMap.comp_apply, PiTensorProduct.map_tprod, finiteEmbed_tprod]
  rfl
end GroundTheory.Automorphic.RestrictedTensor
