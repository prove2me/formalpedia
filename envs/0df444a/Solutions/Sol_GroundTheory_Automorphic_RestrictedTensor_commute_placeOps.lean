-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.commute_placeOps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:45:25.709158+00:00
-- url     : https://prove2.me/submissions/7a6e30e4-53af-4b57-852b-ae89bdee2a57

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Irreducible
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_LocalComponent
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Places
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_singleHom_apply_of_ne
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_commute_singleHom
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_heckeOp_single_mul

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
theorem _root_.solution {v w : ι} (hvw : v ≠ w) :
    ∀ a ∈ placeOps hρ hK'c hK'o hK'e v, ∀ b ∈ placeOps hρ hK'c hK'o hK'e w, Commute a b := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  have h1 := heckeOp_single_mul hρ hK'c hK'o hK'e v x (b := singleHom K w y)
    (singleHom_apply_of_ne y hvw)
  have h2 := heckeOp_single_mul hρ hK'c hK'o hK'e w y (b := singleHom K v x)
    (singleHom_apply_of_ne x hvw.symm)
  show _ * _ = _ * _
  rw [← h1, ← h2, commute_singleHom x (singleHom_apply_of_ne y hvw)]
end GroundTheory.Automorphic.RestrictedTensor
