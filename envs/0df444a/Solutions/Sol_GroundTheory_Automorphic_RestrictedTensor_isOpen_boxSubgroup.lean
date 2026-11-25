-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.isOpen_boxSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:04:26.575565+00:00
-- url     : https://prove2.me/submissions/d6133d07-3c4a-412c-8bd9-14f7c865aebf

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TotallyDisconnectedSpaceRestrictedProduct
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_mem_boxSubgroup

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
theorem _root_.solution [hKo : Fact (∀ v, IsOpen (K v : Set (G v)))]
    {K' : ∀ v, Subgroup (G v)} (hK'o : ∀ v, IsOpen (K' v : Set (G v)))
    (hK' : ∀ᶠ v in cofinite, K' v = K v) :
    IsOpen (boxSubgroup K K' : Set (Πʳ v, [G v, K v])) := by
  classical
  set F := (Filter.eventually_cofinite.1 hK').toFinset
  have heq : (boxSubgroup K K' : Set (Πʳ v, [G v, K v])) =
      {g : Πʳ v, [G v, K v] | ∀ v, v ∉ F → g.1 v ∈ (K v : Set (G v))} ∩
        ⋂ v ∈ F, (fun g : Πʳ v, [G v, K v] => g v) ⁻¹' (K' v : Set (G v)) := by
    ext g
    simp only [SetLike.mem_coe, mem_boxSubgroup, mem_inter_iff, mem_setOf_eq, mem_iInter,
      mem_preimage]
    constructor
    · intro h
      refine ⟨fun v hv => ?_, fun v _ => h v⟩
      have : K' v = K v := by simpa [F] using hv
      rw [← this]
      exact h v
    · rintro ⟨h1, h2⟩ v
      by_cases hv : v ∈ F
      · exact h2 v hv
      · have : K' v = K v := by simpa [F] using hv
        rw [this]
        exact h1 v hv
  rw [heq]
  refine (RestrictedProduct.isOpen_forall_imp_mem hKo.out).inter ?_
  exact isOpen_biInter_finset fun v _ => (hK'o v).preimage (RestrictedProduct.continuous_eval v)
end GroundTheory.Automorphic.RestrictedTensor
