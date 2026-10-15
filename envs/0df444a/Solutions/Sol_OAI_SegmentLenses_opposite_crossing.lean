-- Prove2me | solution 1 for OAI.SegmentLenses.opposite_crossing
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T21:27:02.288739+00:00
-- url     : https://prove2.me/submissions/b7f3d491-df13-4567-aa4a-782b01f685b5

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SegmentLenses/TreeGeometry.lean:L428-L504
-- (upload_full_project.md Phase 4): solution for node OAI.SegmentLenses.opposite_crossing. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_MidpointLenses
import Definitions.Def_OAI_Analysis_SegmentLenses_Basic
import Definitions.Def_OAI_Analysis_SegmentLenses_TreeGeometry
import Theorems.Thm_OAI_SegmentLenses_selected_split_budget
import Theorems.Thm_OAI_SegmentLenses_split_interval

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

theorem split_disjoint (a c b : V) : Disjoint (Finset.Ico a c) (Finset.Icc c b) := by
  have _ := decidableEqV
  have _ := treeOrderV
  have _ := segmentSystemV
  have _ := intervalSegmentsV
  refine Finset.disjoint_left.mpr ?_
  intro v hv hv'
  exact (not_lt_of_ge (Finset.mem_Icc.mp hv').1) (Finset.mem_Ico.mp hv).2

theorem head_zero_above {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    {p : V →₀ ℝ} (hp : p.support ⊆ H) {g v : V} (hg : g ∉ H) (hgv : g ≤ v) :
    p v = 0 := by
  have _ := decidableEqV
  have _ := locallyFiniteOrderV
  have _ := treeOrderV
  have _ := segmentSystemV
  have _ := intervalSegmentsV
  apply Finsupp.notMem_support_iff.mp
  intro hv
  exact hg (hH (hp hv) hgv)

theorem segment_sum_eq_head {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    {p : V →₀ ℝ} (hp : p.support ⊆ H) {a g b : V}
    (hag : a ≤ g) (hgb : g ≤ b) (hg : g ∉ H) :
    (∑ v ∈ Finset.Icc a b, p v) = ∑ v ∈ Finset.Ico a g, p v := by
  classical
  rw [← split_interval hag hgb, Finset.sum_union (split_disjoint _ _ _)]
  have hz : (∑ v ∈ Finset.Icc g b, p v) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    exact head_zero_above hH hp hg (Finset.mem_Icc.mp hv).1
  rw [hz, add_zero]

theorem split_suffix_sum {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    {p : V →₀ ℝ} (hp : p.support ⊆ H) {c g b b' : V}
    (hcg : c ≤ g) (hgb : g ≤ b) (hgb' : g ≤ b') (hg : g ∉ H) :
    (∑ v ∈ Finset.Icc c b, p v) = ∑ v ∈ Finset.Icc c b', p v := by
  rw [segment_sum_eq_head hH hp hcg hgb hg,
    segment_sum_eq_head hH hp hcg hgb' hg]

theorem opposite_split_gain {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    {p : V →₀ ℝ} (hp : p.support ⊆ H) {a c g b b' : V}
    (hac : a ≤ c) (hcg : c ≤ g) (hgb : g ≤ b) (hgb' : g ≤ b')
    (hg : g ∉ H)
    (hop : (∑ v ∈ Finset.Icc a b, p v) * (∑ v ∈ Finset.Icc c b', p v) < 0) :
    2 * |(∑ v ∈ Finset.Icc a b, p v) * (∑ v ∈ Finset.Icc c b', p v)| ≤
      (∑ v ∈ Finset.Ico a c, p v) ^ 2 + (∑ v ∈ Finset.Icc c b, p v) ^ 2 -
        (∑ v ∈ Finset.Icc a b, p v) ^ 2 := by
  classical
  have he := split_suffix_sum hH hp hcg hgb hgb' hg
  have hsum : (∑ v ∈ Finset.Icc a b, p v) =
      (∑ v ∈ Finset.Ico a c, p v) + (∑ v ∈ Finset.Icc c b, p v) := by
    rw [← split_interval hac (le_trans hcg hgb),
      Finset.sum_union (split_disjoint _ _ _)]
  rw [abs_of_neg hop, ← he, hsum]
  nlinarith [sq_nonneg (∑ v ∈ Finset.Icc c b, p v)]

theorem matched_opposite_crossing {ι κ Γ : Type*} [Fintype ι] [Fintype κ] [Fintype Γ]
    {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    (p : V →₀ ℝ) (hp : p.support ⊆ H)
    (a b : ι → V) (a' b' : κ → V)
    (hab : ∀ i, a i ≤ b i) (hab' : ∀ j, a' j ≤ b' j)
    (hd : Pairwise fun i j => Disjoint (Finset.Icc (a i) (b i)) (Finset.Icc (a j) (b j)))
    (hd' : Pairwise fun i j => Disjoint (Finset.Icc (a' i) (b' i)) (Finset.Icc (a' j) (b' j)))
    (gate : Γ → V) (left : Γ → ι) (right : Γ → κ)
    (hl : Function.Injective left) (hr : Function.Injective right)
    (hgate : ∀ g, gate g ∉ H)
    (hmem : ∀ g, a (left g) ≤ gate g ∧ gate g ≤ b (left g))
    (hmem' : ∀ g, a' (right g) ≤ gate g ∧ gate g ≤ b' (right g))
    (hop : ∀ g, (∑ v ∈ Finset.Icc (a (left g)) (b (left g)), p v) *
      (∑ v ∈ Finset.Icc (a' (right g)) (b' (right g)), p v) < 0) :
    2 * ∑ g, |(∑ v ∈ Finset.Icc (a (left g)) (b (left g)), p v) *
        (∑ v ∈ Finset.Icc (a' (right g)) (b' (right g)), p v)| ≤
      (segmentSeminorm V p ^ 2 - ∑ i, (∑ v ∈ Finset.Icc (a i) (b i), p v) ^ 2) +
      (segmentSeminorm V p ^ 2 - ∑ j, (∑ v ∈ Finset.Icc (a' j) (b' j), p v) ^ 2) := by
  classical
  let longer : Γ → Prop := fun g => a (left g) ≤ a' (right g)
  let cost : Γ → ℝ := fun g => 2 *
    |(∑ v ∈ Finset.Icc (a (left g)) (b (left g)), p v) *
      (∑ v ∈ Finset.Icc (a' (right g)) (b' (right g)), p v)|
  have hc : ∀ g, 0 ≤ cost g := fun g => mul_nonneg (by norm_num) (abs_nonneg _)
  have h₁ := selected_split_budget p a b hab hd
    (fun g : {g // longer g} => left g.val) (hl.comp Subtype.val_injective)
    (fun g => a' (right g.val))
    (fun g => ⟨g.property, le_trans (hmem' g.val).1 (hmem g.val).2⟩)
    (fun g => cost g.val) (fun g => hc g.val)
    (fun g => opposite_split_gain hH hp g.property (hmem' g.val).1
      (hmem g.val).2 (hmem' g.val).2 (hgate g.val) (hop g.val))
  have h₂ := selected_split_budget p a' b' hab' hd'
    (fun g : {g // ¬longer g} => right g.val) (hr.comp Subtype.val_injective)
    (fun g => a (left g.val))
    (fun g => ⟨(TreeOrder.lower_chain (hmem g.val).1 (hmem' g.val).1).resolve_left g.property,
      le_trans (hmem g.val).1 (hmem' g.val).2⟩)
    (fun g => cost g.val) (fun g => hc g.val) (fun g => by
      have hstart := (TreeOrder.lower_chain (hmem g.val).1 (hmem' g.val).1).resolve_left g.property
      have ho : (∑ v ∈ Finset.Icc (a' (right g.val)) (b' (right g.val)), p v) *
          (∑ v ∈ Finset.Icc (a (left g.val)) (b (left g.val)), p v) < 0 := by
        simpa [mul_comm] using hop g.val
      simpa only [cost, mul_comm] using opposite_split_gain hH hp hstart
        (hmem g.val).1 (hmem' g.val).2 (hmem g.val).2 (hgate g.val) ho)
  have hs := Fintype.sum_subtype_add_sum_subtype longer cost
  have he : (∑ g, cost g) =
      2 * ∑ g, |(∑ v ∈ Finset.Icc (a (left g)) (b (left g)), p v) *
        (∑ v ∈ Finset.Icc (a' (right g)) (b' (right g)), p v)| := by
    simp [cost, Finset.mul_sum]
  linarith

theorem gates_incomparable {H : Finset V} {g g' : V}
    (hg : Gate H g) (hg' : Gate H g') (h : g ≤ g') : g = g' := by
  have _ := locallyFiniteOrderV
  have _ := treeOrderV
  have _ := segmentSystemV
  have _ := intervalSegmentsV
  by_contra hne
  exact hg.1 (hg'.2 g (lt_of_le_of_ne h hne))

theorem gate_unique_in_interval {H : Finset V} {g g' a b : V}
    (hg : Gate H g) (hg' : Gate H g')
    (hm : g ∈ Finset.Icc a b) (hm' : g' ∈ Finset.Icc a b) : g = g' := by
  rcases TreeOrder.lower_chain (Finset.mem_Icc.mp hm).2 (Finset.mem_Icc.mp hm').2 with h | h
  · exact gates_incomparable hg hg' h
  · exact (gates_incomparable hg' hg h).symm

namespace SegmentFamily

theorem first_le_last (F : SegmentFamily V) (S : F.sets) : F.first S ≤ F.last S := by
  have _ := decidableEqV
  have _ := treeOrderV
  exact
    (F.presentation S).property.1

theorem repr_disjoint (F : SegmentFamily V) :
    Pairwise fun S T : F.sets =>
      Disjoint (Finset.Icc (F.first S) (F.last S)) (Finset.Icc (F.first T) (F.last T)) := by
  intro S T hne
  rw [← F.repr S, ← F.repr T]
  exact F.disjoint S.property T.property (fun h => hne (Subtype.ext h))

theorem boundary_of_mem (F : SegmentFamily V) (p : V →₀ ℝ)
    {g : V} (S : F.sets) (hg : g ∈ S.val) :
    F.boundary p g = ∑ v ∈ S.val, p v := by
  have _ := partialOrderV
  have _ := locallyFiniteOrderV
  have _ := treeOrderV
  have _ := intervalSegmentsV
  classical
  unfold boundary
  rw [Finset.sum_eq_single S.val]
  · simp [hg]
  · intro T hT hne
    have hn : g ∉ T := fun h =>
      Finset.disjoint_left.mp (F.disjoint hT S.property hne) h hg
    simp [hn]
  · intro hn
    exact False.elim (hn S.property)

theorem boundary_nonzero (F : SegmentFamily V) (p : V →₀ ℝ)
    {g : V} (hne : F.boundary p g ≠ 0) : ∃ S : F.sets, g ∈ S.val := by
  have _ := partialOrderV
  have _ := locallyFiniteOrderV
  have _ := treeOrderV
  have _ := intervalSegmentsV
  classical
  by_contra h
  apply hne
  apply Finset.sum_eq_zero
  intro S hS
  have hn : g ∉ S := fun hs => h ⟨⟨S, hS⟩, hs⟩
  simp [hn]

theorem gate_unique {H : Finset V} (F : SegmentFamily V) (S : F.sets)
    {g g' : V} (hg : Gate H g) (hg' : Gate H g') (hm : g ∈ S.val) (hm' : g' ∈ S.val) :
    g = g' := by
  rw [F.repr S] at hm hm'
  exact gate_unique_in_interval hg hg' hm hm'

end SegmentFamily

theorem opposite_crossing (F F' : SegmentFamily V) {H : Finset V}
    (hH : Ancestral (· ≤ ·) H) (p : V →₀ ℝ) (hp : p.support ⊆ H)
    (G : Finset V) (hG : ∀ g ∈ G, Gate H g) :
    (∑ g : G, (|F.boundary p g.val * F'.boundary p g.val| -
      F.boundary p g.val * F'.boundary p g.val)) ≤
      (segmentSeminorm V p ^ 2 - F.seminorm p ^ 2) +
      (segmentSeminorm V p ^ 2 - F'.seminorm p ^ 2) := by
  classical
  let opposite : G → Prop := fun g => F.boundary p g.val * F'.boundary p g.val < 0
  let Γ := {g : G // opposite g}
  have hleft : ∀ g : Γ, ∃ S : F.sets, g.val.val ∈ S.val := by
    intro g
    apply F.boundary_nonzero p
    intro hz
    have ho := g.property
    change F.boundary p g.val.val * F'.boundary p g.val.val < 0 at ho
    rw [hz, zero_mul] at ho
    exact lt_irrefl _ ho
  have hright : ∀ g : Γ, ∃ S : F'.sets, g.val.val ∈ S.val := by
    intro g
    apply F'.boundary_nonzero p
    intro hz
    have ho := g.property
    change F.boundary p g.val.val * F'.boundary p g.val.val < 0 at ho
    rw [hz, mul_zero] at ho
    exact lt_irrefl _ ho
  let left : Γ → F.sets := fun g => Classical.choose (hleft g)
  let right : Γ → F'.sets := fun g => Classical.choose (hright g)
  have hlmem : ∀ g : Γ, g.val.val ∈ (left g).val := fun g => Classical.choose_spec (hleft g)
  have hrmem : ∀ g : Γ, g.val.val ∈ (right g).val := fun g => Classical.choose_spec (hright g)
  have hl : Function.Injective left := by
    intro g g' he
    apply Subtype.ext
    apply Subtype.ext
    have hg' := hlmem g'
    rw [← he] at hg'
    exact F.gate_unique (left g) (hG _ g.val.property) (hG _ g'.val.property) (hlmem g) hg'
  have hr : Function.Injective right := by
    intro g g' he
    apply Subtype.ext
    apply Subtype.ext
    have hg' := hrmem g'
    rw [← he] at hg'
    exact F'.gate_unique (right g) (hG _ g.val.property) (hG _ g'.val.property) (hrmem g) hg'
  have heL : ∀ g : Γ, (∑ v ∈ Finset.Icc (F.first (left g)) (F.last (left g)), p v) =
      F.boundary p g.val.val := by
    intro g
    rw [← F.repr (left g)]
    exact (F.boundary_of_mem p (left g) (hlmem g)).symm
  have heR : ∀ g : Γ, (∑ v ∈ Finset.Icc (F'.first (right g)) (F'.last (right g)), p v) =
      F'.boundary p g.val.val := by
    intro g
    rw [← F'.repr (right g)]
    exact (F'.boundary_of_mem p (right g) (hrmem g)).symm
  have h := matched_opposite_crossing hH p hp F.first F.last F'.first F'.last
    F.first_le_last F'.first_le_last F.repr_disjoint F'.repr_disjoint
    (fun g : Γ => g.val.val) left right hl hr
    (fun g => (hG _ g.val.property).1)
    (fun g => Finset.mem_Icc.mp ((F.repr (left g)) ▸ hlmem g))
    (fun g => Finset.mem_Icc.mp ((F'.repr (right g)) ▸ hrmem g))
    (fun g => by rw [heL, heR]; exact g.property)
  simp_rw [heL, heR, ← F.repr, ← F'.repr] at h
  rw [← F.seminorm_sq p, ← F'.seminorm_sq p] at h
  have hsum : (∑ g : G, (|F.boundary p g.val * F'.boundary p g.val| -
        F.boundary p g.val * F'.boundary p g.val)) =
      2 * ∑ g : Γ, |F.boundary p g.val.val * F'.boundary p g.val.val| := by
    have he : ∀ z : ℝ, |z| - z = if z < 0 then 2 * |z| else 0 := by
      intro z
      by_cases hz : z < 0
      · simp [hz, abs_of_neg hz]; ring
      · simp [hz, abs_of_nonneg (le_of_not_gt hz)]
    simp_rw [he]
    rw [← Finset.sum_filter]
    rw [Finset.sum_subtype (p := opposite) _ (fun g => by simp [opposite])]
    rw [← Finset.mul_sum]
  rw [hsum]
  exact h

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

theorem solution (F F' : SegmentFamily V) {H : Finset V}
    (hH : Ancestral (· ≤ ·) H) (p : V →₀ ℝ) (hp : p.support ⊆ H)
    (G : Finset V) (hG : ∀ g ∈ G, Gate H g) :
    (∑ g : G, (|F.boundary p g.val * F'.boundary p g.val| -
      F.boundary p g.val * F'.boundary p g.val)) ≤
      (segmentSeminorm V p ^ 2 - F.seminorm p ^ 2) +
      (segmentSeminorm V p ^ 2 - F'.seminorm p ^ 2) := by
  first
    | exact OAI.SegmentLenses.opposite_crossing F F' hH p hp G hG
    | exact OAI.SegmentLenses.opposite_crossing
    | (apply OAI.SegmentLenses.opposite_crossing <;> assumption)
    | (intros; apply OAI.SegmentLenses.opposite_crossing <;> assumption)
