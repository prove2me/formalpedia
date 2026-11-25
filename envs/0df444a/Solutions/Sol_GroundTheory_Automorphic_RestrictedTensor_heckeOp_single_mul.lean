-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.heckeOp_single_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:27:01.939896+00:00
-- url     : https://prove2.me/submissions/a3d80d4e-96a6-489f-a18b-1507880b70cb

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Irreducible
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_LocalComponent
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Places
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_eraseAt_apply_self
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_single_mul_eraseAt
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_eraseAt_mem_boxSubgroup
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_commute_singleHom
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_heckeOp_mul_apply
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
include hK'c hK'o hK'e
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution (v : ι) (x : G v) {b : Πʳ w, [G w, K w]} (hb : b v = 1) :
    heckeOp hρ (isCompact_boxSubgroup_of_eq hK'c hK'e) (isOpen_boxSubgroup hK'o hK'e)
        (singleHom K v x * b) =
      heckeOp hρ (isCompact_boxSubgroup_of_eq hK'c hK'e) (isOpen_boxSubgroup hK'o hK'e)
          (singleHom K v x) *
        heckeOp hρ (isCompact_boxSubgroup_of_eq hK'c hK'e) (isOpen_boxSubgroup hK'o hK'e) b := by
  ext m
  rw [Module.End.mul_apply, heckeOp_mul_apply]
  intro h hh
  refine ⟨eraseAt v h, eraseAt_mem_boxSubgroup v hh, ?_, ?_⟩
  · exact (commute_singleHom x (eraseAt_apply_self v h)).symm
  · have h1 : (eraseAt v h)⁻¹ * h = singleHom K v (h v) := by
      have hc := commute_singleHom (K := K) (h v) (eraseAt_apply_self v h)
      calc (eraseAt v h)⁻¹ * h = (eraseAt v h)⁻¹ * (singleHom K v (h v) * eraseAt v h) := by
            rw [single_mul_eraseAt]
        _ = singleHom K v (h v) := by rw [hc, inv_mul_cancel_left]
    rw [h1]
    exact commute_singleHom (h v) hb
end GroundTheory.Automorphic.RestrictedTensor
