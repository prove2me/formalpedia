-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.isCompact_boxSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:59:27.576029+00:00
-- url     : https://prove2.me/submissions/3a3888c8-c615-49ad-93c5-686a82986a6b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TotallyDisconnectedSpaceRestrictedProduct

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
open Filter Function Set Topology
open scoped RestrictedProduct
variable {ι : Type*} {G : ι → Type*} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  {K : ∀ v, Subgroup (G v)}
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution {K' : ∀ v, Subgroup (G v)}
    (hK'c : ∀ v, IsCompact (K' v : Set (G v))) (hK' : ∀ᶠ v in cofinite, K' v ≤ K v) :
    IsCompact (boxSubgroup K K' : Set (Πʳ v, [G v, K v])) := by
  set S : Set ι := {v | K' v ≤ K v}
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.2 hK'
  set C : Set (Πʳ v, [G v, K v]_[𝓟 S]) :=
    ((↑) : (Πʳ v, [G v, K v]_[𝓟 S]) → ∀ v, G v) ⁻¹' (Set.pi univ fun v => (K' v : Set (G v)))
  have hC : IsCompact C := by
    refine (RestrictedProduct.isEmbedding_coe_of_principal.isInducing.isCompact_preimage_iff
      ?_).2 (isCompact_univ_pi hK'c)
    rw [RestrictedProduct.range_coe_principal]
    intro f hf v hv
    exact hv (hf v (mem_univ v))
  have heq : (boxSubgroup K K' : Set (Πʳ v, [G v, K v])) =
      RestrictedProduct.inclusion G (fun v => (K v : Set (G v))) hS '' C := by
    ext g
    constructor
    · intro hg
      refine ⟨⟨g.1, Filter.eventually_principal.2 fun v hv => hv (hg v)⟩, fun v _ => hg v, ?_⟩
      rfl
    · rintro ⟨h, hh, rfl⟩ v
      exact hh v (mem_univ v)
  rw [heq]
  exact hC.image (RestrictedProduct.continuous_inclusion hS)
end GroundTheory.Automorphic.RestrictedTensor
