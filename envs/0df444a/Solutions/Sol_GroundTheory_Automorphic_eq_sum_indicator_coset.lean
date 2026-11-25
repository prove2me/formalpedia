-- Prove2me | solution 1 for GroundTheory.Automorphic.eq_sum_indicator_coset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:08:49.6488+00:00
-- url     : https://prove2.me/submissions/8d9c56e0-3e4b-49ae-a31d-55e5b229492d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact
import Theorems.Thm_GroundTheory_Automorphic_mk_eq_iff_mem_out_smul
import Theorems.Thm_GroundTheory_Automorphic_apply_eq_of_mem_smul

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
open Set Filter Topology
open scoped Pointwise
variable {G : Type*} [Group G] {E : Type*}
variable [TopologicalSpace G] [IsTopologicalGroup G] {R : Type*} [Semiring R] [AddCommMonoid E]
  [Module R E]
namespace GroundTheory.Automorphic
theorem _root_.solution (K : OpenSubgroup G) {f : G → E} (hf : HasCompactSupport f)
    (hK : ∀ g, ∀ k ∈ K, f (g * k) = f g) :
    f = ∑ x ∈ (finite_image_mk_tsupport K hf).toFinset,
      (x.out • (K : Set G)).indicator (fun _ => f x.out) := by
  classical
  funext y
  rw [Finset.sum_apply]
  by_cases hy : (y : G ⧸ (K : Subgroup G)) ∈ (finite_image_mk_tsupport K hf).toFinset
  · rw [Finset.sum_eq_single (y : G ⧸ (K : Subgroup G))]
    · have hmem : y ∈ (y : G ⧸ (K : Subgroup G)).out • (K : Set G) :=
        (mk_eq_iff_mem_out_smul (K : Subgroup G) _ y).1 rfl
      rw [Set.indicator_of_mem hmem]
      exact apply_eq_of_mem_smul hK hmem
    · intro b _ hb
      exact Set.indicator_of_notMem
        (fun h => hb ((mk_eq_iff_mem_out_smul (K : Subgroup G) b y).2 h).symm) _
    · intro h
      exact absurd hy h
  · rw [Finset.sum_eq_zero]
    · by_contra h
      exact hy ((Set.Finite.mem_toFinset _).2 ⟨y, subset_tsupport f h, rfl⟩)
    · intro b hb
      refine Set.indicator_of_notMem (fun h => hy ?_) _
      rwa [(mk_eq_iff_mem_out_smul (K : Subgroup G) b y).2 h]
end GroundTheory.Automorphic
