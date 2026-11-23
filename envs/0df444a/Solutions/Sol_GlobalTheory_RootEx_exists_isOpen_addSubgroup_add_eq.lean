-- Prove2me | solution 1 for GlobalTheory.RootEx.exists_isOpen_addSubgroup_add_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:08:38.26022+00:00
-- url     : https://prove2.me/submissions/027e41eb-25b2-43f6-bb3f-cdefe83a9545

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology
open GlobalTheory GlobalTheory.RootEx
open MeasureTheory ValuativeRel Matrix
open scoped Topology Pointwise
namespace GlobalTheory.RootEx
namespace _root_.GlobalTheory.RootEx
theorem _root_.solution {X : Type*}
    [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] {Φ : X → ℂ} (hlc : IsLocallyConstant Φ) (hcs : IsCompact (tsupport Φ)) :
    ∃ Λ : AddSubgroup X, IsOpen (Λ : Set X) ∧ ∀ x, ∀ y ∈ Λ, Φ (x + y) = Φ x := by
  classical
  obtain ⟨t, ht⟩ := hcs.elim_finite_subcover (fun c : ℂ => {x | Φ x = c})
    (fun c => hlc.isOpen_fiber c) (fun x _ => Set.mem_iUnion.2 ⟨Φ x, rfl⟩)
  have hV : ∀ c : ℂ, ∃ V ∈ 𝓝 (0 : X), c ≠ 0 → {x | Φ x = c} + V ⊆ {x | Φ x = c} := by
    intro c
    by_cases hc : c = 0
    · exact ⟨Set.univ, Filter.univ_mem, fun h => (h hc).elim⟩
    · have hsub : {x | Φ x = c} ⊆ tsupport Φ := fun x hx =>
        subset_tsupport Φ (by
          rw [Function.mem_support]
          rw [Set.mem_setOf_eq] at hx
          rw [hx]
          exact hc)
      obtain ⟨V, hV0, hVs⟩ := compact_open_separated_add_right
        (hcs.of_isClosed_subset (hlc.isClosed_fiber c) hsub) (hlc.isOpen_fiber c) le_rfl
      exact ⟨V, hV0, fun _ => hVs⟩
  choose V hV0 hVsub using hV
  have hW : (⋂ c ∈ t, (V c ∩ -V c)) ∈ 𝓝 (0 : X) :=
    (Filter.biInter_finset_mem t).2 fun c _ =>
      Filter.inter_mem (hV0 c) (neg_mem_nhds_zero X (hV0 c))
  have hstep : ∀ x, ∀ v ∈ (⋂ c ∈ t, (V c ∩ -V c)), Φ (x + v) = Φ x := by
    intro x v hv
    have hv' : ∀ c ∈ t, v ∈ V c ∧ -v ∈ V c := by
      intro c hc
      have h := Set.mem_iInter₂.1 hv c hc
      exact ⟨h.1, Set.mem_neg.1 h.2⟩
    by_cases h0 : Φ x = 0
    · by_contra hne
      have hne' : Φ (x + v) ≠ 0 := by rwa [h0] at hne
      have hxK : x + v ∈ tsupport Φ := subset_tsupport Φ hne'
      obtain ⟨c, hct, hc⟩ := Set.mem_iUnion₂.1 (ht hxK)
      have hc' : Φ (x + v) = c := hc
      have hc0 : c ≠ 0 := hc' ▸ hne'
      have h := hVsub c hc0 (Set.add_mem_add hc (hv' c hct).2)
      have h' : Φ (x + v + -v) = c := h
      rw [add_neg_cancel_right] at h'
      exact hc0 (h'.symm.trans h0)
    · have hxK : x ∈ tsupport Φ := subset_tsupport Φ h0
      obtain ⟨c, hct, hc⟩ := Set.mem_iUnion₂.1 (ht hxK)
      have hc' : Φ x = c := hc
      have hc0 : c ≠ 0 := hc' ▸ h0
      have h := hVsub c hc0 (Set.add_mem_add hc (hv' c hct).1)
      have h' : Φ (x + v) = c := h
      exact h'.trans hc'.symm
  refine ⟨AddSubgroup.closure (⋂ c ∈ t, (V c ∩ -V c)),
    AddSubgroup.isOpen_of_mem_nhds _ (g := 0)
      (Filter.mem_of_superset hW AddSubgroup.subset_closure), ?_⟩
  intro x y hy
  induction hy using AddSubgroup.closure_induction generalizing x with
  | mem y hy => exact hstep x y hy
  | zero => simp
  | add y z _ _ hy hz => rw [← add_assoc, hz, hy]
  | neg y _ hy =>
    have h := hy (x + -y)
    rw [neg_add_cancel_right] at h
    exact h.symm
end _root_.GlobalTheory.RootEx
end GlobalTheory.RootEx
