-- Prove2me | solution 1 for GlobalTheory.LocFlat.CFac.Span.mem_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:14:06.207103+00:00
-- url     : https://prove2.me/submissions/dea76ef2-fd4b-4e5b-9964-381ab113f93d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ProdFnMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SpanSchwartzBruhatProductEqTop
import Theorems.Thm_GlobalTheory_LocFlat_CFac_Span_F_mem
import Theorems.Thm_GlobalTheory_LocFlat_CFac_Span_exists_compact_clopen
import Theorems.Thm_GlobalTheory_LocFlat_CFac_mulLC_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LocFlat.CFac.mulLC_apply



set_option autoImplicit false
open GlobalTheory.SplitWeil GlobalTheory.LocFlat.CFac
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.CFac GlobalTheory.LocFlat.CFac.Span
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
namespace GlobalTheory.LocFlat.CFac.Span
theorem _root_.solution [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
    [T2Space Y] [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y]
    (F : X × Y → ℂ) (hF : F ∈ SB (X × Y)) : F ∈ S X Y := by
  have hbox : ∀ p : X × Y, ∃ r : Set X × Set Y, IsBox r ∧ p ∈ r.1 ×ˢ r.2 ∧
      ∀ q ∈ r.1 ×ˢ r.2, F q = F p := by
    intro p
    have hO : IsOpen {q | F q = F p} := hF.1.isOpen_fiber _
    obtain ⟨u, v, hu, hv, hpu, hpv, huv⟩ := isOpen_prod_iff.1 hO p.1 p.2 rfl
    obtain ⟨U₁, hU1, hU2, hU3, hU4⟩ := exists_compact_clopen hu hpu
    obtain ⟨V₁, hV1, hV2, hV3, hV4⟩ := exists_compact_clopen hv hpv
    exact ⟨(U₁, V₁), ⟨hU1, hU2, hV1, hV2⟩, ⟨hU3, hV3⟩, fun q hq => huv (Set.prod_mono hU4 hV4 hq)⟩
  choose R hRb hRp hRc using hbox
  obtain ⟨t, -, ht⟩ := hF.2.isCompact.elim_nhds_subcover (fun p => (R p).1 ×ˢ (R p).2)
    fun p _ => ((hRb p).2.1.isOpen.prod (hRb p).2.2.2.isOpen).mem_nhds (hRp p)
  have hsub : tsupport F ⊆ U (t.toList.map R) := by
    intro q hq
    have := ht hq
    simp only [Set.mem_iUnion] at this
    obtain ⟨p, hp, hq'⟩ := this
    simp only [U, Set.mem_iUnion]
    exact ⟨R p, List.mem_map.2 ⟨p, Finset.mem_toList.2 hp, rfl⟩, hq'⟩
  have heq : (U (t.toList.map R)).indicator F = F :=
    Set.indicator_eq_self.2 ((subset_tsupport F).trans hsub)
  rw [← heq]
  refine F_mem F _ ?_
  intro r hr
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 hr
  exact ⟨hRb p, F p, hRc p⟩
end GlobalTheory.LocFlat.CFac.Span
