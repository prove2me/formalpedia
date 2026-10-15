-- Prove2me | solution 1 for OAI.SegmentLenses.SegmentFamily.clip_seminorm
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T21:31:19.025145+00:00
-- url     : https://prove2.me/submissions/cef7283f-60f6-4e7d-867a-c102b0cb12b0

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SegmentLenses/Pairing.lean:L330-L343
-- (upload_full_project.md Phase 4): solution for node OAI.SegmentLenses.SegmentFamily.clip_seminorm. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_MidpointLenses
import Definitions.Def_OAI_Analysis_SegmentLenses_Basic
import Definitions.Def_OAI_Analysis_SegmentLenses_TreeGeometry
import Definitions.Def_OAI_Analysis_SegmentLenses_FiniteLaws
import Definitions.Def_OAI_Analysis_SegmentLenses_Pairing

-- ---- from OAI.Analysis.SegmentLenses.Pairing ----
namespace OAI

/-!
# Finite heads and the completion–dual pairing
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

section Restrictions
variable {V : Type*} [decidableEqV : DecidableEq V] [PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V]

end Restrictions

section Pairing
variable {V : Type*} [SegmentSystem V]

end Pairing

section MorePairing
variable {V : Type*} [decidableEqV : DecidableEq V] [SegmentSystem V]

end MorePairing

section DualRestrictions
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V]

end DualRestrictions

section IndexedFamilies
variable {V ι : Type*} [DecidableEq V] [SegmentSystem V] [Fintype ι]

theorem SegmentFamily.ofPieces_sq (S : ι → Finset V)
    (hS : ∀ i, S i = ∅ ∨ SegmentSystem.isSegment (S i))
    (hd : Pairwise fun i j => Disjoint (S i) (S j)) (p : V →₀ ℝ) :
    (ofPieces S hS hd).seminorm p ^ 2 = ∑ i, (∑ v ∈ S i, p v) ^ 2 := by
  classical
  rw [seminorm_sq, Finset.sum_coe_sort (ofPieces S hS hd).sets
    (fun T : Finset V => (∑ v ∈ T, p v) ^ 2)]
  change (∑ T ∈ (Finset.univ.image S).erase ∅, (∑ v ∈ T, p v) ^ 2) = _
  rw [Finset.sum_erase _ (by simp)]
  apply Finset.sum_image_of_pairwise_eq_zero
  intro i hi j hj hij heq
  have hempty : S i = ∅ := by
    have hh : Disjoint (S i) (S j) := hd hij
    rw [← heq] at hh
    exact disjoint_self.mp hh
  simp [hempty]

end IndexedFamilies

section ClipFamilies
variable {V : Type*} [DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

theorem SegmentFamily.clip_seminorm {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    (F : SegmentFamily V) (p : V →₀ ℝ) (hp : p.support ⊆ H) :
    (F.clip hH).seminorm p = F.seminorm p := by
  have he : (F.clip hH).seminorm p ^ 2 = F.seminorm p ^ 2 := by
    rw [clip, ofPieces_sq, F.seminorm_sq]
    apply Finset.sum_congr rfl
    intro S hS
    congr 1
    apply Finset.sum_subset Finset.inter_subset_left
    intro v hv hnv
    apply Finsupp.notMem_support_iff.mp
    intro hvs
    exact hnv (Finset.mem_inter.mpr ⟨hv, hp hvs⟩)
  nlinarith [apply_nonneg (F.clip hH).seminorm p, apply_nonneg F.seminorm p]

end ClipFamilies

end SegmentLenses

end

end OAI

-- ---- platform node ----
open OAI OAI.SegmentLenses
open scoped BigOperators
open Finset
variable {V : Type*} [DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

theorem solution {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    (F : SegmentFamily V) (p : V →₀ ℝ) (hp : p.support ⊆ H) :
    (F.clip hH).seminorm p = F.seminorm p := by
  first
    | exact OAI.SegmentLenses.SegmentFamily.clip_seminorm hH F p hp
    | exact OAI.SegmentLenses.SegmentFamily.clip_seminorm
    | (apply OAI.SegmentLenses.SegmentFamily.clip_seminorm <;> assumption)
    | (intros; apply OAI.SegmentLenses.SegmentFamily.clip_seminorm <;> assumption)
