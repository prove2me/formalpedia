-- Prove2me | solution 1 for GlobalTheory.locallyConstant_compactSupport_invariant_openAddSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:19:08.5599+00:00
-- url     : https://prove2.me/submissions/925c75c6-90d8-4716-98b8-03255b6a67b1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyConstantCompactSupportInvariantOpenAddSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Filter Topology
namespace GlobalTheory
theorem _root_.solution :
    ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
      [NonarchimedeanAddGroup X] (g : X → ℂ), IsLocallyConstant g → HasCompactSupport g →
      ∃ H : OpenAddSubgroup X, ∀ z, ∀ a ∈ H, g (z + a) = g z := by
  intro X _ _ _ _ g hg hc
  have key : ∀ z : X, ∃ V : OpenAddSubgroup X, ∀ h ∈ V, g (z + h) = g z := by
    intro z
    have hT : Tendsto (fun h : X => z + h) (𝓝 0) (𝓝 z) := by
      have := (continuous_add_left z).tendsto (0 : X)
      simpa using this
    have hn : {h : X | g (z + h) = g z} ∈ 𝓝 (0 : X) := hT.eventually (hg.eventually_eq z)
    obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hn
    exact ⟨V, fun h hh => hV hh⟩
  choose H hH using key
  have hU : ∀ j y, y - j ∈ H j → g y = g j := by
    intro j y h
    have := hH j (y - j) h
    have e : j + (y - j) = y := by abel
    rwa [e] at this
  obtain ⟨t, ht⟩ := hc.isCompact.elim_finite_subcover (fun z : X => {y : X | y - z ∈ H z})
    (fun z => (H z).isOpen.preimage (continuous_id.sub continuous_const))
    (fun y _ => Set.mem_iUnion.2 ⟨y, by simp⟩)
  refine ⟨t.inf H, fun z a ha => ?_⟩
  have hle : ∀ j ∈ t, a ∈ H j := fun j hj => Finset.inf_le (f := H) hj ha
  by_cases hz : z ∈ tsupport g
  · obtain ⟨j, hj, hzj⟩ := Set.mem_iUnion₂.1 (ht hz)
    have h1 : z - j ∈ H j := hzj
    have h2 : z + a - j ∈ H j := by
      have := (H j).add_mem h1 (hle j hj)
      have e : z - j + a = z + a - j := by abel
      rwa [e] at this
    rw [hU j _ h2, hU j _ h1]
  by_cases hza : z + a ∈ tsupport g
  · obtain ⟨j, hj, hzj⟩ := Set.mem_iUnion₂.1 (ht hza)
    have h1 : z + a - j ∈ H j := hzj
    have h2 : z - j ∈ H j := by
      have := (H j).sub_mem h1 (hle j hj)
      have e : z + a - j - a = z - j := by abel
      rwa [e] at this
    rw [hU j _ h2, hU j _ h1]
  rw [image_eq_zero_of_notMem_tsupport hz, image_eq_zero_of_notMem_tsupport hza]
end GlobalTheory
