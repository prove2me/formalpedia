-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.exists_isCompact_isOpen_inter_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:41.399856+00:00
-- url     : https://prove2.me/submissions/87d6fb37-8bef-4423-a293-6edc52bb8b76

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_isCompact_isOpen_between

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
theorem _root_.solution {U O A : Set X} (hU : IsOpen U) (hOU : O ⊆ U)
    (hAO : A ⊆ O) (hAc : IsCompact A) (hAo : IsOpen ((Subtype.val : O → X) ⁻¹' A)) :
    ∃ B : Set X, IsCompact B ∧ IsOpen B ∧ B ⊆ U ∧ B ∩ O = A := by
  obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.1 hAo
  have hAV : A ⊆ V := fun x hx => by
    have : (⟨x, hAO hx⟩ : O) ∈ (Subtype.val : O → X) ⁻¹' V := by rw [hV]; exact hx
    exact this
  obtain ⟨B, hBc, hBo, hAB, hBV⟩ :=
    exists_isCompact_isOpen_between hAc (hVo.inter hU) (subset_inter hAV (hAO.trans hOU))
  refine ⟨B, hBc, hBo, hBV.trans inter_subset_right, subset_antisymm ?_ ?_⟩
  · rintro x ⟨hxB, hxO⟩
    have : (⟨x, hxO⟩ : O) ∈ (Subtype.val : O → X) ⁻¹' V := (hBV hxB).1
    rw [hV] at this
    exact this
  · exact fun x hx => ⟨hAB hx, hAO hx⟩
end GroundTheory.Automorphic.Whittaker
