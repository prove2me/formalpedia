-- Prove2me | solution 1 for GroundTheory.Global.Artin.sum_conj_eq_sum_subgroupOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:48.15536+00:00
-- url     : https://prove2.me/submissions/9ab5a71b-d505-4b89-8980-7868cd95dc33

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_Mackey
import Definitions.Def_GroundTheory_GlobalFields_Artin_MackeyFrobenius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped Pointwise
open GroundTheory GroundTheory.Global GroundTheory.Global.Artin
open GroundTheory.LocalField
variable {G : Type*} [Group G]
variable {H D I : Subgroup G}
namespace GroundTheory.Global.Artin
theorem _root_.solution (H I : Subgroup G) [Fintype I] (x : G)
    [Fintype ((MulAut.conj x • I : Subgroup G).subgroupOf H)] (F : G → ℂ)
    (hF : ∀ g ∉ H, F g = 0) :
    ∑ i : I, F (x * i * x⁻¹) =
      ∑ j : (MulAut.conj x • I : Subgroup G).subgroupOf H, F ((j : H) : G) := by
  classical
  rw [← Finset.sum_filter_of_ne (p := fun i : I ↦ x * i * x⁻¹ ∈ H)
    (fun i _ hne ↦ by
      by_contra h
      exact hne (hF _ h))]
  refine Finset.sum_bij' (fun i hi ↦ ⟨⟨x * i * x⁻¹, (Finset.mem_filter.1 hi).2⟩, ?_⟩)
    (fun j _ ↦ ⟨x⁻¹ * ((j : H) : G) * x,
      (mem_conj_smul_iff I x _).1 (Subgroup.mem_subgroupOf.1 j.2)⟩) ?_ ?_ ?_ ?_ ?_
  · rename_i i hi
    rw [Subgroup.mem_subgroupOf, mem_conj_smul_iff]
    change x⁻¹ * (x * (i : G) * x⁻¹) * x ∈ I
    rw [show x⁻¹ * (x * (i : G) * x⁻¹) * x = i by group]
    exact i.2
  · intro i _
    exact Finset.mem_univ _
  · intro j _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    change x * (x⁻¹ * ((j : H) : G) * x) * x⁻¹ ∈ H
    rw [show x * (x⁻¹ * ((j : H) : G) * x) * x⁻¹ = (j : H) by group]
    exact (j : H).2
  · intro i _
    apply Subtype.ext
    change x⁻¹ * (x * (i : G) * x⁻¹) * x = i
    group
  · intro j _
    apply Subtype.ext
    apply Subtype.ext
    change x * (x⁻¹ * ((j : H) : G) * x) * x⁻¹ = (j : H)
    group
  · intro i _
    rfl
end GroundTheory.Global.Artin
