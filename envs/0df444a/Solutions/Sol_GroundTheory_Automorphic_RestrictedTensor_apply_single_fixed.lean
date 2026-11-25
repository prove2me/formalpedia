-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.apply_single_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:27:09.493153+00:00
-- url     : https://prove2.me/submissions/de7ea292-85f9-4c96-a5c0-e9228e568582

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Irreducible
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_LocalComponent
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Places
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_commute_singleHom

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
open Filter Function Module Set
open scoped RestrictedProduct
variable {ι : Type*} {G : ι → Type*} [∀ v, Group (G v)] {K : ∀ v, Subgroup (G v)}
variable [∀ v, TopologicalSpace (G v)] [∀ v, IsTopologicalGroup (G v)]
  [∀ v, LocallyCompactSpace (G v)] [∀ v, T2Space (G v)] [∀ v, TotallyDisconnectedSpace (G v)]
  [hKo : Fact (∀ v, IsOpen (K v : Set (G v)))] [hKc : ∀ v, CompactSpace (K v)]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (Πʳ v, [G v, K v]) V}
  (hρ : IsSmooth ρ) {K' : ∀ v, Subgroup (G v)} (hK'c : ∀ v, IsCompact (K' v : Set (G v)))
  (hK'o : ∀ v, IsOpen (K' v : Set (G v))) (hK'e : ∀ᶠ v in cofinite, K' v = K v)
variable [DecidableEq ι]
omit hK'c hK'o hK'e
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution (v : ι) (x : G v) {m : V} (hm : m ∈ fixedVectors ρ (boxSubgroup K K'))
    {h : Πʳ w, [G w, K w]} (hh : h ∈ boxSubgroup K K') (hv : h v = 1) :
    ρ h (ρ (singleHom K v x) m) = ρ (singleHom K v x) m := by
  rw [← Module.End.mul_apply, ← map_mul, ← commute_singleHom x hv, map_mul, Module.End.mul_apply,
    hm h hh]
end GroundTheory.Automorphic.RestrictedTensor
