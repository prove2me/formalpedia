-- Prove2me | solution 1 for GlobalTheory.JR.AbsInv.exists_nhds_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:20.437682+00:00
-- url     : https://prove2.me/submissions/4ec85bbf-2b09-448a-86c2-e891254830cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSelfDualOfDualSubgroups

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.AbsInv
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
open MeasureTheory Filter Topology Pointwise
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
namespace GlobalTheory.JR.AbsInv
namespace _root_.GlobalTheory.JR.AbsInv
theorem _root_.solution {f : V → ℂ}
    (hf : _root_.GlobalTheory.JR.IsTest f) :
    ∃ U ∈ 𝓝 (0 : V), ∀ M : AddSubgroup V, (M : Set V) ⊆ U → ∀ x, ∀ m ∈ M, f (x + m) = f x := by
  have hf' : IsLocallyConstant f ∧ HasCompactSupport f := hf
  obtain ⟨hlc, hcs⟩ := hf'
  have hK : IsCompact (tsupport f) := hcs
  have hfin : (f '' tsupport f).Finite := by
    haveI : CompactSpace (tsupport f) := isCompact_iff_compactSpace.mp hK
    have hloc : IsLocallyConstant (f ∘ ((↑) : tsupport f → V)) :=
      hlc.comp_continuous continuous_subtype_val
    have := hloc.range_finite
    rwa [Set.range_comp, Subtype.range_coe] at this
  have hW : ∀ c : ℂ, ∃ W ∈ 𝓝 (0 : V), c ≠ 0 → {x | f x = c} + W ⊆ {x | f x = c} := by
    intro c
    by_cases hc : c = 0
    · exact ⟨Set.univ, univ_mem, fun h => (h hc).elim⟩
    · have hsub : {x | f x = c} ⊆ tsupport f := by
        intro x hx
        apply subset_tsupport f
        rw [Function.mem_support, show f x = c from hx]
        exact hc
      obtain ⟨W, hW0, hWs⟩ := compact_open_separated_add_right
        (hK.of_isClosed_subset (hlc.isClosed_fiber c) hsub) (hlc.isOpen_fiber c) subset_rfl
      exact ⟨W, hW0, fun _ => hWs⟩
  choose W hW0 hWsub using hW
  refine ⟨⋂ c ∈ f '' tsupport f, W c, (biInter_mem hfin).2 fun c _ => hW0 c, ?_⟩
  have key : ∀ x m, m ∈ ⋂ c ∈ f '' tsupport f, W c → f x ≠ 0 → f (x + m) = f x := by
    intro x m hm hx
    have hxK : x ∈ tsupport f := subset_tsupport f (Function.mem_support.2 hx)
    have hmW : m ∈ W (f x) := Set.mem_iInter₂.1 hm (f x) ⟨x, hxK, rfl⟩
    exact hWsub (f x) hx (Set.add_mem_add (show x ∈ {y | f y = f x} from rfl) hmW)
  intro M hM x m hmM
  by_cases hx : f x = 0
  · by_contra hne
    have h1 := key (x + m) (-m) (hM (neg_mem hmM)) (fun h => hne (h.trans hx.symm))
    rw [add_neg_cancel_right] at h1
    exact hne h1.symm
  · exact key x m (hM hmM) hx
end _root_.GlobalTheory.JR.AbsInv
end GlobalTheory.JR.AbsInv
