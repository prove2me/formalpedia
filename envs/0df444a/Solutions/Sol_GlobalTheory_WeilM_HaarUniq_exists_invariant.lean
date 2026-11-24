-- Prove2me | solution 1 for GlobalTheory.WeilM.HaarUniq.exists_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:52:00.582381+00:00
-- url     : https://prove2.me/submissions/0abb8e59-ce29-4649-bcf3-ada4928efd8c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.WeilM GlobalTheory.WeilM.HaarUniq
variable {V : Type} [AddCommGroup V] [TopologicalSpace V]
open MeasureTheory Filter Topology
variable {V : Type} [AddCommGroup V] [TopologicalSpace V]
namespace GlobalTheory.WeilM.HaarUniq
namespace _root_.GlobalTheory.WeilM.HaarUniq
theorem _root_.solution [NonarchimedeanAddGroup V] {φ : V → ℂ}
    (hφ : φ ∈ _root_.GlobalTheory.WeilM.SB V) :
    ∃ K : OpenAddSubgroup V, ∀ k ∈ K, ∀ x, φ (x + k) = φ x := by
  have hφ' : IsLocallyConstant φ ∧ HasCompactSupport φ := by
    simpa [_root_.GlobalTheory.WeilM.SB] using hφ
  obtain ⟨hlc, hcs⟩ := hφ'
  have hnhds : ∀ x : V, (fun w => x + w) ⁻¹' {y | φ y = φ x} ∈ 𝓝 (0 : V) := by
    intro x
    refine (continuous_const_add x).continuousAt.preimage_mem_nhds ?_
    rw [add_zero]
    exact (hlc.isOpen_fiber (φ x)).mem_nhds rfl
  choose W hW using fun x => NonarchimedeanAddGroup.is_nonarchimedean _ (hnhds x)
  have hval : ∀ i y, y - i ∈ W i → φ y = φ i := by
    intro i y hy
    have := hW i hy
    simpa using this
  obtain ⟨t, ht⟩ := hcs.isCompact.elim_finite_subcover (fun i => (fun y => y - i) ⁻¹' (W i))
    (fun i => (W i).isOpen.preimage (continuous_sub_right i))
    (fun y _ => Set.mem_iUnion.2 ⟨y, by simpa using (W y).zero_mem⟩)
  refine ⟨t.inf W, fun k hk x => ?_⟩
  have hkW : ∀ i ∈ t, k ∈ W i := fun i hi => (Finset.inf_le hi : t.inf W ≤ W i) hk
  by_cases hx : x ∈ tsupport φ
  · obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (ht hx)
    have hxi' : x - i ∈ W i := hxi
    have hxk : x + k - i ∈ W i := by
      have := (W i).add_mem hxi' (hkW i hi)
      rwa [sub_add_eq_add_sub] at this
    rw [hval i _ hxk, hval i _ hxi']
  by_cases hxk : x + k ∈ tsupport φ
  · obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (ht hxk)
    have hxi' : x + k - i ∈ W i := hxi
    have hx' : x - i ∈ W i := by
      have := (W i).sub_mem hxi' (hkW i hi)
      rwa [sub_right_comm, add_sub_cancel_right] at this
    rw [hval i _ hxi', hval i _ hx']
  rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxk]
end _root_.GlobalTheory.WeilM.HaarUniq
end GlobalTheory.WeilM.HaarUniq
