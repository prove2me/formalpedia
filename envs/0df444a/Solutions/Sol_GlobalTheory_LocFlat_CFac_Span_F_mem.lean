-- Prove2me | solution 1 for GlobalTheory.LocFlat.CFac.Span.F_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:54:07.657441+00:00
-- url     : https://prove2.me/submissions/eff8b424-e82b-4e55-8723-44dfaed9cccb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ProdFnMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SpanSchwartzBruhatProductEqTop
import Theorems.Thm_GlobalTheory_LocFlat_CFac_Span_IsBox_inter
import Theorems.Thm_GlobalTheory_LocFlat_CFac_Span_box_mem
import Theorems.Thm_GlobalTheory_LocFlat_CFac_Span_U_cons
import Theorems.Thm_GlobalTheory_LocFlat_CFac_Span_inter_U
import Theorems.Thm_GlobalTheory_LocFlat_CFac_Span_U_mem
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
theorem _root_.solution (F : X × Y → ℂ) : ∀ L : List (Set X × Set Y),
    (∀ r ∈ L, IsBox r ∧ ∃ c : ℂ, ∀ p ∈ r.1 ×ˢ r.2, F p = c) → (U L).indicator F ∈ S X Y := by
  intro L
  induction L with
  | nil => intro _; simp [U]; exact Submodule.zero_mem _
  | cons r L ih =>
    intro hL
    obtain ⟨hB, c, hc⟩ := hL r (by simp)
    have key := Set.indicator_union_add_inter (f := F) (r.1 ×ˢ r.2) (U L)
    have hA : (r.1 ×ˢ r.2).indicator F = c • (r.1 ×ˢ r.2).indicator (1 : X × Y → ℂ) := by
      ext p
      simp only [Pi.smul_apply]
      by_cases hp : p ∈ r.1 ×ˢ r.2
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]; simp [hc p hp]
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp]; simp
    have hI : (r.1 ×ˢ r.2 ∩ U L).indicator F = c • (r.1 ×ˢ r.2 ∩ U L).indicator (1 : X × Y → ℂ) := by
      ext p
      simp only [Pi.smul_apply]
      by_cases hp : p ∈ r.1 ×ˢ r.2 ∩ U L
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]; simp [hc p hp.1]
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp]; simp
    rw [U_cons, eq_sub_of_add_eq key, hA, hI, inter_U]
    refine Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ c (box_mem hB))
      (ih fun s hs => hL s (by simp [hs]))) (Submodule.smul_mem _ c (U_mem _ _ le_rfl ?_))
    intro s hs
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
    exact hB.inter (hL t (by simp [ht])).1
end GlobalTheory.LocFlat.CFac.Span
