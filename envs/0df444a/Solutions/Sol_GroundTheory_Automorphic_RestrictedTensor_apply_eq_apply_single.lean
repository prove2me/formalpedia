-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.apply_eq_apply_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:27:08.058832+00:00
-- url     : https://prove2.me/submissions/a2bcc615-5c5c-4643-b811-cd867c7db356

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Irreducible
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_LocalComponent
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Places
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_eraseAt_apply_self
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_single_mul_eraseAt
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_eraseAt_mem_boxSubgroup

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
theorem _root_.solution (v : ι) {u : V}
    (hu : ∀ h ∈ boxSubgroup K K', h v = 1 → ρ h u = u) {h : Πʳ w, [G w, K w]}
    (hh : h ∈ boxSubgroup K K') : ρ h u = ρ (singleHom K v (h v)) u := by
  conv_lhs => rw [← single_mul_eraseAt v h]
  rw [map_mul, Module.End.mul_apply, hu _ (eraseAt_mem_boxSubgroup v hh) (eraseAt_apply_self v h)]
end GroundTheory.Automorphic.RestrictedTensor
