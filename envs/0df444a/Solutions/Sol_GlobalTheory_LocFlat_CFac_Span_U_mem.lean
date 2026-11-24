-- Prove2me | solution 1 for GlobalTheory.LocFlat.CFac.Span.U_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:38:52.447463+00:00
-- url     : https://prove2.me/submissions/5cc17c61-7d64-410c-9c39-08f0e588bfb7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ProdFnMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SpanSchwartzBruhatProductEqTop
import Theorems.Thm_GlobalTheory_LocFlat_CFac_Span_IsBox_inter
import Theorems.Thm_GlobalTheory_LocFlat_CFac_Span_box_mem
import Theorems.Thm_GlobalTheory_LocFlat_CFac_Span_U_cons
import Theorems.Thm_GlobalTheory_LocFlat_CFac_Span_inter_U
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
theorem _root_.solution : ∀ (n : ℕ) (L : List (Set X × Set Y)), L.length ≤ n → (∀ r ∈ L, IsBox r) →
    (U L).indicator (1 : X × Y → ℂ) ∈ S X Y := by
  intro n
  induction n with
  | zero =>
    intro L hL _
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hL)]
    simp [U]
    exact Submodule.zero_mem _
  | succ n ih =>
    intro L hL hB
    cases L with
    | nil => simp [U]; exact Submodule.zero_mem _
    | cons r L =>
      have key := Set.indicator_union_add_inter (f := (1 : X × Y → ℂ)) (r.1 ×ˢ r.2) (U L)
      have hL' : L.length ≤ n := by simp at hL; omega
      rw [U_cons, eq_sub_of_add_eq key, inter_U]
      refine Submodule.sub_mem _ (Submodule.add_mem _ (box_mem (hB r (by simp)))
        (ih L hL' fun s hs => hB s (by simp [hs]))) (ih _ (by simpa using hL') ?_)
      intro s hs
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
      exact (hB r (by simp)).inter (hB t (by simp [ht]))
end GlobalTheory.LocFlat.CFac.Span
