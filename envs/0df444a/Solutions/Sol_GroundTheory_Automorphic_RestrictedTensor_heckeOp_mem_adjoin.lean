-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.heckeOp_mem_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:37:46.246804+00:00
-- url     : https://prove2.me/submissions/6674ade1-a07a-4aac-956a-dd1ce46ce557

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Irreducible
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_LocalComponent
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Places
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_eraseAt_apply_self
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_eraseAt_apply_of_ne
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_single_mul_eraseAt
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_heckeOp_single_mul
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_heckeOp_of_mem
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
theorem _root_.solution (s : Finset ι) {g : Πʳ w, [G w, K w]} (hg : ∀ v ∉ s, g v ∈ K' v) :
    heckeOp hρ (isCompact_boxSubgroup_of_eq hK'c hK'e) (isOpen_boxSubgroup hK'o hK'e) g ∈
      Algebra.adjoin ℂ (⋃ v ∈ s, placeOps hρ hK'c hK'o hK'e v) := by
  induction s using Finset.induction_on generalizing g with
  | empty =>
    rw [heckeOp_of_mem _ _ _ (show g ∈ boxSubgroup K K' from fun v => hg v (Finset.notMem_empty v))]
    exact Subalgebra.one_mem _
  | insert a s has ih =>
    have herase : ∀ v ∉ s, eraseAt a g v ∈ K' v := by
      intro v hv
      by_cases hva : v = a
      · subst hva; rw [eraseAt_apply_self]; exact (K' v).one_mem
      · rw [eraseAt_apply_of_ne _ hva]
        exact hg v (by simp [hva, hv])
    have hmono : Algebra.adjoin ℂ (⋃ v ∈ s, placeOps hρ hK'c hK'o hK'e v) ≤
        Algebra.adjoin ℂ (⋃ v ∈ insert a s, placeOps hρ hK'c hK'o hK'e v) :=
      Algebra.adjoin_mono (biUnion_subset_biUnion_left (by simp))
    rw [← single_mul_eraseAt a g, heckeOp_single_mul hρ hK'c hK'o hK'e a (g a)
      (eraseAt_apply_self a g)]
    refine Subalgebra.mul_mem _ (Algebra.subset_adjoin ?_) (hmono (ih herase))
    exact mem_biUnion (Finset.mem_insert_self a s) ⟨g a, rfl⟩
end GroundTheory.Automorphic.RestrictedTensor
