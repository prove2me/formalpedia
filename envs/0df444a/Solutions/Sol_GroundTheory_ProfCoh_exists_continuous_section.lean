-- Prove2me | solution 1 for GroundTheory.ProfCoh.exists_continuous_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:48:53.8438+00:00
-- url     : https://prove2.me/submissions/6ed08c50-b50a-4165-8040-0a96c6fe7ae7

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
import Definitions.Def_GroundTheory_ProfiniteCohomology_InflationRestriction_Section
import Theorems.Thm_GroundTheory_ProfCoh_exists_closed_transversal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open Topology
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G]
variable [TotallyDisconnectedSpace G]
namespace GroundTheory.ProfCoh
theorem _root_.solution (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    ∃ s : G ⧸ N → G, Continuous s ∧ (∀ c, (s c : G ⧸ N) = c) ∧ s 1 = 1 := by
  have : IsClosed (N : Set G) := hN
  have : T2Space (G ⧸ N) := inferInstance
  obtain ⟨T, hTc, hex, huniq⟩ := exists_closed_transversal N hN
  have : CompactSpace T := isCompact_iff_compactSpace.mp hTc.isCompact
  let f : T → G ⧸ N := fun t => (t : G)
  have hf : Function.Bijective f := by
    refine ⟨fun t t' h => Subtype.ext (huniq t t.2 t' t'.2 h), fun c => ?_⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
    obtain ⟨t, ht, htx⟩ := hex x
    exact ⟨⟨t, ht⟩, htx⟩
  let e : T ≃ₜ G ⧸ N := (QuotientGroup.continuous_mk.comp continuous_subtype_val :
    Continuous f).homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hf)
  let s₀ : G ⧸ N → G := fun c => (e.symm c : G)
  have hs₀ : ∀ c, (s₀ c : G ⧸ N) = c := fun c => e.apply_symm_apply c
  have h1 : s₀ 1 ∈ N := by
    have := hs₀ 1
    rw [← QuotientGroup.mk_one, QuotientGroup.eq] at this
    simpa using this
  refine ⟨fun c => s₀ c * (s₀ 1)⁻¹,
    (continuous_subtype_val.comp e.symm.continuous).mul continuous_const, fun c => ?_, ?_⟩
  · calc ((s₀ c * (s₀ 1)⁻¹ : G) : G ⧸ N) = (s₀ c : G ⧸ N) :=
          QuotientGroup.eq.mpr (by convert h1 using 1; group)
      _ = c := hs₀ c
  · exact mul_inv_cancel _
end GroundTheory.ProfCoh
