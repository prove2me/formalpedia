-- Prove2me | solution 1 for OAI.SegmentLenses.selected_split_budget
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T21:25:40.590041+00:00
-- url     : https://prove2.me/submissions/63cb7668-e8f5-4fe2-a911-bbface561b77

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SegmentLenses/TreeGeometry.lean:L205-L271
-- (upload_full_project.md Phase 4): solution for node OAI.SegmentLenses.selected_split_budget. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_MidpointLenses
import Definitions.Def_OAI_Analysis_SegmentLenses_Basic
import Definitions.Def_OAI_Analysis_SegmentLenses_TreeGeometry
import Theorems.Thm_OAI_SegmentLenses_refinement_test_bound

-- ---- from OAI.Analysis.SegmentLenses.TreeGeometry ----
namespace OAI

/-!
# Ancestry, segment splitting, and opposite crossings
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

section TreeGeometry
variable {V : Type*} [decidableEqV : DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [segmentSystemV : SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

theorem interval_isSegment {a b : V} (hab : a ≤ b) :
    SegmentSystem.isSegment (Finset.Icc a b) := by
  have _ := decidableEqV
  have _ := treeOrderV
  apply (IntervalSegments.iff_interval _).mpr
  exact ⟨a, b, hab, fun v => Finset.mem_Icc⟩

theorem halfOpen_isSegment (a c : V) :
    Finset.Ico a c = ∅ ∨ SegmentSystem.isSegment (Finset.Ico a c) := by
  classical
  by_cases hac : a < c
  · right
    have hne : (Finset.Ico a c).Nonempty := ⟨a, Finset.mem_Ico.mpr ⟨le_rfl, hac⟩⟩
    obtain ⟨z, hz⟩ := Finset.exists_maximal hne
    have hzac := Finset.mem_Ico.mp hz.1
    have hmax : ∀ v ∈ Finset.Ico a c, v ≤ z := by
      intro v hv
      have hvac := Finset.mem_Ico.mp hv
      rcases TreeOrder.lower_chain hvac.2.le hzac.2.le with hvz | hzv
      · exact hvz
      · exact hz.2 hv hzv
    have he : Finset.Ico a c = Finset.Icc a z := by
      ext v
      constructor
      · intro hv
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp hv).1, hmax v hv⟩
      · intro hv
        have hh := Finset.mem_Icc.mp hv
        exact Finset.mem_Ico.mpr ⟨hh.1, lt_of_le_of_lt hh.2 hzac.2⟩
    rw [he]
    exact interval_isSegment hzac.1
  · left
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hh := Finset.mem_Ico.mp hv
    exact hac (lt_of_le_of_lt hh.1 hh.2)

theorem split_disjoint (a c b : V) : Disjoint (Finset.Ico a c) (Finset.Icc c b) := by
  have _ := decidableEqV
  have _ := treeOrderV
  have _ := segmentSystemV
  have _ := intervalSegmentsV
  refine Finset.disjoint_left.mpr ?_
  intro v hv hv'
  exact (not_lt_of_ge (Finset.mem_Icc.mp hv').1) (Finset.mem_Ico.mp hv).2

theorem selected_split_budget {ι Γ : Type*} [Fintype ι] [Fintype Γ]
    (p : V →₀ ℝ) (a b : ι → V) (hab : ∀ i, a i ≤ b i)
    (hd : Pairwise fun i j => Disjoint (Finset.Icc (a i) (b i)) (Finset.Icc (a j) (b j)))
    (select : Γ → ι) (hinj : Function.Injective select) (cut : Γ → V)
    (hcut : ∀ g, a (select g) ≤ cut g ∧ cut g ≤ b (select g))
    (cost : Γ → ℝ) (hcost : ∀ g, 0 ≤ cost g)
    (hgain : ∀ g, cost g ≤
      (∑ v ∈ Finset.Ico (a (select g)) (cut g), p v) ^ 2 +
      (∑ v ∈ Finset.Icc (cut g) (b (select g)), p v) ^ 2 -
      (∑ v ∈ Finset.Icc (a (select g)) (b (select g)), p v) ^ 2) :
    ∑ g, cost g ≤ segmentSeminorm V p ^ 2 -
      ∑ i, (∑ v ∈ Finset.Icc (a i) (b i), p v) ^ 2 := by
  classical
  let c := Function.extend select cut a
  have hc : ∀ i, a i ≤ c i ∧ c i ≤ b i := by
    intro i
    by_cases hi : ∃ g, select g = i
    · obtain ⟨g, rfl⟩ := hi
      rw [show c (select g) = cut g from hinj.extend_apply cut a g]
      exact hcut g
    · rw [show c i = a i from Function.extend_apply' cut a i hi]
      exact ⟨le_rfl, hab i⟩
  let gain : ι → ℝ := fun i =>
    (∑ v ∈ Finset.Ico (a i) (c i), p v) ^ 2 +
    (∑ v ∈ Finset.Icc (c i) (b i), p v) ^ 2 -
    (∑ v ∈ Finset.Icc (a i) (b i), p v) ^ 2
  have hgselect : ∀ g, cost g ≤ gain (select g) := by
    intro g
    dsimp [gain]
    rw [show c (select g) = cut g from hinj.extend_apply cut a g]
    exact hgain g
  have hgn : ∀ i, 0 ≤ gain i := by
    intro i
    by_cases hi : ∃ g, select g = i
    · obtain ⟨g, rfl⟩ := hi
      exact (hcost g).trans (hgselect g)
    · dsimp [gain]
      rw [show c i = a i from Function.extend_apply' cut a i hi]
      simp
  have hs : ∑ g, cost g ≤ ∑ i, gain i := by
    calc
      ∑ g, cost g ≤ ∑ g, gain (select g) := Finset.sum_le_sum fun g _ => hgselect g
      _ = ∑ i ∈ Finset.univ.image select, gain i :=
        (Finset.sum_image hinj.injOn).symm
      _ ≤ ∑ i, gain i := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun i _ _ => hgn i)
  have he := refinement_test_bound p
    (fun i => Finset.Icc (a i) (b i))
    (fun i => Finset.Ico (a i) (c i)) (fun i => Finset.Icc (c i) (b i)) hd
    (fun i => by
      intro v hv
      have hh := Finset.mem_Ico.mp hv
      exact Finset.mem_Icc.mpr ⟨hh.1, le_trans hh.2.le (hc i).2⟩)
    (fun i => by
      intro v hv
      have hh := Finset.mem_Icc.mp hv
      exact Finset.mem_Icc.mpr ⟨le_trans (hc i).1 hh.1, hh.2⟩)
    (fun i => split_disjoint _ _ _)
    (fun i => halfOpen_isSegment _ _)
    (fun i => Or.inr (interval_isSegment (hc i).2))
  have hsum : (∑ i, gain i) =
      (∑ i, ((∑ v ∈ Finset.Ico (a i) (c i), p v) ^ 2 +
        (∑ v ∈ Finset.Icc (c i) (b i), p v) ^ 2)) -
      ∑ i, (∑ v ∈ Finset.Icc (a i) (b i), p v) ^ 2 := by
    simp [gain, Finset.sum_sub_distrib]
  rw [hsum] at hs
  linarith

namespace SegmentFamily

end SegmentFamily

end TreeGeometry

end SegmentLenses

end

end OAI

-- ---- platform node ----
open OAI OAI.SegmentLenses
open scoped BigOperators
open Finset
variable {V : Type*} [decidableEqV : DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [segmentSystemV : SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

theorem solution {ι Γ : Type*} [Fintype ι] [Fintype Γ]
    (p : V →₀ ℝ) (a b : ι → V) (hab : ∀ i, a i ≤ b i)
    (hd : Pairwise fun i j => Disjoint (Finset.Icc (a i) (b i)) (Finset.Icc (a j) (b j)))
    (select : Γ → ι) (hinj : Function.Injective select) (cut : Γ → V)
    (hcut : ∀ g, a (select g) ≤ cut g ∧ cut g ≤ b (select g))
    (cost : Γ → ℝ) (hcost : ∀ g, 0 ≤ cost g)
    (hgain : ∀ g, cost g ≤
      (∑ v ∈ Finset.Ico (a (select g)) (cut g), p v) ^ 2 +
      (∑ v ∈ Finset.Icc (cut g) (b (select g)), p v) ^ 2 -
      (∑ v ∈ Finset.Icc (a (select g)) (b (select g)), p v) ^ 2) :
    ∑ g, cost g ≤ segmentSeminorm V p ^ 2 -
      ∑ i, (∑ v ∈ Finset.Icc (a i) (b i), p v) ^ 2 := by
  first
    | exact OAI.SegmentLenses.selected_split_budget p a b hab hd select hinj cut hcut cost hcost hgain
    | exact OAI.SegmentLenses.selected_split_budget
    | (apply OAI.SegmentLenses.selected_split_budget <;> assumption)
    | (intros; apply OAI.SegmentLenses.selected_split_budget <;> assumption)
