-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.fixedProj_single_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:37:44.538079+00:00
-- url     : https://prove2.me/submissions/dada3878-17cc-489d-94bb-9319fe418aa7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Irreducible
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_LocalComponent
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Places
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_singleHom_mem_boxSubgroup
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_apply_eq_apply_single
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_fixedProj_comp_eq
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_isOpen_boxSubgroup


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
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution (v : ι) (hρv : IsSmooth (ρ.comp (singleHom K v))) {u : V}
    (hu : ∀ h ∈ boxSubgroup K K', h v = 1 → ρ h u = u) :
    (fixedProj (ρ.comp (singleHom K v)) hρv (hK'c v) (hK'o v) u : V) =
      fixedProj ρ hρ (isCompact_boxSubgroup_of_eq hK'c hK'e) (isOpen_boxSubgroup hK'o hK'e) u :=
  fixedProj_comp_eq (singleHom K v) hρ hρv _ _ (hK'c v) (hK'o v)
    (fun k hk => singleHom_mem_boxSubgroup hk)
    (fun h hh => ⟨h v, hh v, apply_eq_apply_single v hu hh⟩)
end GroundTheory.Automorphic.RestrictedTensor
