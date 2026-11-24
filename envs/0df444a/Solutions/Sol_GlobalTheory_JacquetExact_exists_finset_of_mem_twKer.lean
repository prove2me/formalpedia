-- Prove2me | solution 1 for GlobalTheory.JacquetExact.exists_finset_of_mem_twKer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:11:56.323209+00:00
-- url     : https://prove2.me/submissions/95eeded5-ebe8-49d5-844a-a6a92830e1ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviEmbMulSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InSupportOfIsSubquotient
import Theorems.Thm_GlobalTheory_IwahoriInj_sub_mem_twKer


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)
open GlobalTheory GlobalTheory.JacquetExact
variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.JacquetExact
theorem _root_.solution {τ : Representation ℂ G W} {N : Subgroup G} {w : W}
    (hw : w ∈ twKer τ N 1) :
    ∃ S : Finset G, (∀ u ∈ S, u ∈ N) ∧ ∀ H : Subgroup G, (∀ u ∈ S, u ∈ H) → w ∈ twKer τ H 1 := by
  classical
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, v, rfl⟩ := hx
    refine ⟨{(u : G)}, by simp, fun H hH => ?_⟩
    simpa using GlobalTheory.IwahoriInj.sub_mem_twKer (π := τ) (hH u (by simp)) v
  | zero => exact ⟨∅, by simp, fun _ _ => zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨S, hS, hx⟩ := hx
    obtain ⟨T, hT, hy⟩ := hy
    refine ⟨S ∪ T, fun u hu => (Finset.mem_union.1 hu).elim (hS u) (hT u), fun H hH => add_mem
      (hx H fun u hu => hH u (Finset.mem_union_left _ hu))
      (hy H fun u hu => hH u (Finset.mem_union_right _ hu))⟩
  | smul c x _ hx =>
    obtain ⟨S, hS, hx⟩ := hx
    exact ⟨S, hS, fun H hH => Submodule.smul_mem _ c (hx H hH)⟩
end GlobalTheory.JacquetExact
