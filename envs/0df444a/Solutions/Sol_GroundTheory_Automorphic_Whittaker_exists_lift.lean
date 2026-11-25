-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:02:09.182235+00:00
-- url     : https://prove2.me/submissions/829baf89-e85e-4e17-a7f0-096c725fcc25

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_isCompact_isOpen_inter_eq
import Theorems.Thm_GroundTheory_Automorphic_indicator_mem_locallyConstantCompactSupport
import Theorems.Thm_GroundTheory_Automorphic_isCompact_isOpen_fiber
import Theorems.Thm_GroundTheory_Automorphic_range_finite_of_mem_locallyConstantCompactSupport


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology
variable {X : Type*} [TopologicalSpace X]
variable [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {U O : Set X} (hU : IsOpen U) (hOU : O ⊆ U) {φ : O → ℂ}
    (hφ : φ ∈ locallyConstantCompactSupport O ℂ ℂ) :
    ∃ f ∈ supportedIn U, ∀ x : O, f x = φ x := by
  classical
  have key : ∀ c : ℂ, ∃ B : Set X, IsCompact B ∧ IsOpen B ∧ B ⊆ U ∧
      (c ≠ 0 → ∀ x : O, (x : X) ∈ B ↔ φ x = c) := by
    intro c
    by_cases hc : c = 0
    · exact ⟨∅, isCompact_empty, isOpen_empty, empty_subset _, fun h => absurd hc h⟩
    obtain ⟨hFc, hFo⟩ := isCompact_isOpen_fiber hφ hc
    have hAc : IsCompact ((Subtype.val : O → X) '' {x | φ x = c}) :=
      hFc.image continuous_subtype_val
    have hAo : IsOpen ((Subtype.val : O → X) ⁻¹' ((Subtype.val : O → X) '' {x | φ x = c})) := by
      rwa [preimage_image_eq _ Subtype.val_injective]
    obtain ⟨B, hBc, hBo, hBU, hBO⟩ := exists_isCompact_isOpen_inter_eq hU hOU
      (by rintro _ ⟨x, -, rfl⟩; exact x.2) hAc hAo
    refine ⟨B, hBc, hBo, hBU, fun _ x => ?_⟩
    constructor
    · intro hx
      have : (x : X) ∈ B ∩ O := ⟨hx, x.2⟩
      rw [hBO] at this
      obtain ⟨y, hy, hyx⟩ := this
      rw [← Subtype.ext hyx]
      exact hy
    · intro hx
      have : (x : X) ∈ (Subtype.val : O → X) '' {x | φ x = c} := ⟨x, hx, rfl⟩
      rw [← hBO] at this
      exact this.1
  choose B hBc hBo hBU hBO using key
  have hfin := range_finite_of_mem_locallyConstantCompactSupport hφ
  refine ⟨∑ c ∈ hfin.toFinset.filter (· ≠ 0), (B c).indicator (fun _ => c), ?_, ?_⟩
  · refine Submodule.sum_mem _ fun c _ => ⟨?_, ?_⟩
    · exact indicator_mem_locallyConstantCompactSupport (hBc c) (hBo c) c
    · exact (Set.support_indicator_subset).trans (hBU c)
  · intro x
    rw [Finset.sum_apply]
    by_cases hx : φ x = 0
    · rw [hx]
      refine Finset.sum_eq_zero fun c hc => ?_
      have hc0 : c ≠ 0 := (Finset.mem_filter.1 hc).2
      refine Set.indicator_of_notMem (fun h => hc0 ?_) _
      rw [← hx]
      exact ((hBO c hc0 x).1 h).symm
    · rw [Finset.sum_eq_single (φ x)]
      · exact Set.indicator_of_mem ((hBO _ hx x).2 rfl) _
      · intro c hc hcx
        exact Set.indicator_of_notMem
          (fun h => hcx ((hBO c (Finset.mem_filter.1 hc).2 x).1 h).symm) _
      · intro h
        exact absurd (Finset.mem_filter.2 ⟨(Set.Finite.mem_toFinset _).2 (mem_range_self x), hx⟩) h
end GroundTheory.Automorphic.Whittaker
