-- Prove2me | solution 1 for GlobalTheory.RootEx.exists_mem_SB_eq_one_on_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:42:50.629617+00:00
-- url     : https://prove2.me/submissions/89500080-d989-4ab1-b123-9fbbf41b1b6a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsMemSBEqOneOnCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open GlobalTheory GlobalTheory.RootEx
namespace GlobalTheory.RootEx
theorem _root_.solution (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (C : Set (n → k)) (hC : IsCompact C) :
    ∃ χ ∈ SB (n → k), ∀ u ∈ C, χ u = 1 := by
  classical
  haveI : T2Space k := by
    letI := IsTopologicalAddGroup.rightUniformSpace k
    haveI := isUniformAddGroup_of_addCommGroup (G := k)
    infer_instance
  have ho : IsOpen (𝒪[k] : Set k) := Valuation.isOpen_integer
  have hc : IsCompact (𝒪[k] : Set k) := IsNonarchimedeanLocalField.isCompact_closedBall k 1
  let B : Set (n → k) := Set.univ.pi fun _ => (𝒪[k] : Set k)
  have hBo : IsOpen B := isOpen_set_pi Set.finite_univ fun _ _ => ho
  have hBc : IsCompact B := isCompact_univ_pi fun _ => hc
  let U : (n → k) → Set (n → k) := fun x => (Homeomorph.addLeft x) '' B
  have hUo : ∀ x, IsOpen (U x) := fun x => (Homeomorph.addLeft x).isOpenMap _ hBo
  have hUc : ∀ x, IsCompact (U x) := fun x => hBc.image (Homeomorph.addLeft x).continuous
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover U hUo fun x _ =>
    Set.mem_iUnion.mpr ⟨x, 0, fun _ _ => zero_mem _, by simp⟩
  set K : Set (n → k) := ⋃ x ∈ t, U x with hK
  have hKo : IsOpen K := isOpen_biUnion fun x _ => hUo x
  have hKc : IsCompact K := t.isCompact_biUnion fun x _ => hUc x
  have hcl : IsClopen K := ⟨hKc.isClosed, hKo⟩
  refine ⟨K.indicator fun _ => (1 : ℂ), ⟨?_, ?_⟩, fun u hu => Set.indicator_of_mem (ht hu) _⟩
  · refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
    by_cases hx : x ∈ K
    · filter_upwards [hKo.mem_nhds hx] with y hy
      simp [hx, hy]
    · filter_upwards [hcl.compl.isOpen.mem_nhds hx] with y hy
      simp [hx, Set.notMem_of_mem_compl hy]
  · exact HasCompactSupport.intro hKc fun x hx => Set.indicator_of_notMem hx _
end GlobalTheory.RootEx
