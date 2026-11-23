-- Prove2me | solution 1 for GroundTheory.Automorphic.exists_openSubgroup_isCompact_subset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:07.660867+00:00
-- url     : https://prove2.me/submissions/a990fdfc-59a1-4e59-8386-f80965af0e8d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Theorems.Thm_GroundTheory_Automorphic_exists_isCompact_isOpen_subset

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
open Set Filter Topology MeasureTheory
open scoped Pointwise
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
namespace GroundTheory.Automorphic
theorem _root_.solution {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ U := by
  obtain ⟨W, hWc, hWo, h1W, hWU⟩ := exists_isCompact_isOpen_subset hU
  obtain ⟨V, hV1, hWV⟩ := compact_open_separated_mul_right hWc hWo subset_rfl

  let H : Subgroup G :=
    { carrier := {x | ∀ w, w ∈ W ↔ w * x ∈ W}
      one_mem' := fun w => by simp
      mul_mem' := fun {a b} ha hb w => by rw [ha w, hb (w * a), mul_assoc]
      inv_mem' := fun {a} ha w => by
        have := ha (w * a⁻¹)
        rw [inv_mul_cancel_right] at this
        exact this.symm }
  have hVH : V ∩ V⁻¹ ⊆ (H : Set G) := by
    rintro v ⟨hv, hv'⟩ w
    refine ⟨fun hw => hWV (Set.mul_mem_mul hw hv), fun hw => ?_⟩
    have := hWV (Set.mul_mem_mul hw (Set.mem_inv.1 hv'))
    rwa [mul_inv_cancel_right] at this
  have hHn : (H : Set G) ∈ 𝓝 (1 : G) :=
    mem_of_superset (inter_mem hV1 (inv_mem_nhds_one G hV1)) hVH
  have hHW : (H : Set G) ⊆ W := fun x hx => by
    have := (hx 1).1 h1W
    rwa [one_mul] at this
  let K : OpenSubgroup G := ⟨H, H.isOpen_of_mem_nhds hHn⟩
  exact ⟨K, hWc.of_isClosed_subset K.isClosed hHW, hHW.trans hWU⟩
end GroundTheory.Automorphic
