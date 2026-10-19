-- Prove2me | solution 1 for OAI.DiamondDistortion.Ancestry.replaced_tail_eq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:47:07.350709+00:00
-- url     : https://prove2.me/submissions/3022fd0d-d2fa-4d06-bb40-e9a02df9705a

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/Ancestry.lean:L586-L646
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.Ancestry.replaced_tail_eq. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry

-- ---- from OAI.Analysis.DiamondDistortion.SegmentNorm ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace SegmentSystem
variable {ι : Type*} (T : SegmentSystem ι)

variable {T}

variable (T)

lemma combine_unit_of_mem (F : T.Family) (a : Fin F.n → ℝ)
    (i : Fin F.n) {v : ι} (hv : v ∈ F.seg i) :
    T.combine F.seg a (T.unitVector v) = a i := by
  classical
  rw [combine_unit, Finset.sum_eq_single i]
  · simp only [ite_eq_left hv]
  · intro j _ hji
    rw [ite_eq_right (fun h => Finset.disjoint_left.mp (F.disjoint hji) h hv)]
  · simp

variable {T}

variable (T)

end SegmentSystem

end DiamondDistortion

end

end OAI

-- ---- from OAI.Analysis.DiamondDistortion.Ancestry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace Ancestry
open scoped Classical
variable {ι : Type*} [A : Ancestry ι]
attribute [local instance] OAI.DiamondDistortion.Ancestry.instPartialOrder
lemma interval_chain {S : Finset ι} (hS : A.segments.IsSegment S) :
    ∀ a ∈ S, ∀ b ∈ S, a ≤ b ∨ b ≤ a := by
  obtain ⟨l, r, _, hmem⟩ := hS
  intro a ha b hb
  exact A.predecessors_total ((hmem a).mp ha).2 ((hmem b).mp hb).2

lemma gates_eq_of_le {H : Set ι} {g h : ι} (hg : A.Gate H g)
    (hh : A.Gate H h) (hgh : g ≤ h) : g = h := by
  by_contra hne
  exact hg.1 (hh.2 g (lt_of_le_of_ne hgh hne))

lemma gates_eq_of_common_upper {H : Set ι} {g h v : ι} (hg : A.Gate H g)
    (hh : A.Gate H h) (hgv : g ≤ v) (hhv : h ≤ v) : g = h := by
  rcases A.predecessors_total hgv hhv with h | h
  · exact A.gates_eq_of_le hg hh h
  · exact (A.gates_eq_of_le hh hg h).symm

lemma exists_gate_le {H : Set ι} {K : Finset ι} (hK : A.Ancestral (K : Set ι))
    {v : ι} (hvK : v ∈ K) (hvH : v ∉ H) :
    ∃ g ∈ K, A.Gate H g ∧ g ≤ v := by
  classical
  let S := K.filter (fun a => a ≤ v ∧ a ∉ H)
  have hvS : v ∈ S := by simp [S, hvK, hvH]
  obtain ⟨g, hg, hmin⟩ := Finset.exists_minimal ⟨v, hvS⟩
  have hgK := (Finset.mem_filter.mp hg).1
  have hgv := (Finset.mem_filter.mp hg).2.1
  have hgH := (Finset.mem_filter.mp hg).2.2
  refine ⟨g, hgK, ⟨hgH, ?_⟩, hgv⟩
  intro a hag
  by_contra haH
  have haS : a ∈ S := by
    exact Finset.mem_filter.mpr ⟨hK hag.le hgK, hag.le.trans hgv, haH⟩
  exact (not_le_of_gt hag) (hmin haS hag.le)

lemma first_spec (F : A.segments.Family) (i : Fin F.n) :
    ∃ b, A.first F i ≤ b ∧ ∀ v, v ∈ F.seg i ↔ A.first F i ≤ v ∧ v ≤ b :=
  Classical.choose_spec (F.allowed i)

lemma first_le_of_mem (F : A.segments.Family) (i : Fin F.n) {v : ι}
    (hv : v ∈ F.seg i) : A.first F i ≤ v := by
  obtain ⟨b, _, hm⟩ := A.first_spec F i
  exact ((hm v).mp hv).1

lemma boundaryCoeff_eq (F : A.segments.Family) (p : ι →₀ ℝ)
    (i : Fin F.n) {g : ι} (hg : g ∈ F.seg i) :
    A.boundaryCoeff F p g = ∑ v ∈ F.seg i, p v := by
  classical
  rw [boundaryCoeff, Finset.sum_eq_single i]
  · simp [hg]
  · intro j _ hji
    have hj : g ∉ F.seg j := fun h => Finset.disjoint_left.mp (F.disjoint hji) h hg
    simp [hj]
  · simp

lemma tailAt_eq (F : A.segments.Family) (H : Finset ι)
    (i : Fin F.n) {g : ι} (hg : g ∈ F.seg i) :
    A.tailAt F H g = (F.seg i).filter (· ∉ H) := by
  classical
  have h : ∃ i, g ∈ F.seg i := ⟨i,hg⟩
  have he : h.choose = i := by
    by_contra hn
    exact Finset.disjoint_left.mp (F.disjoint hn) h.choose_spec hg
  simp only [tailAt, dite_eq_left h]
  rw [he]

lemma tailAt_mem {F : A.segments.Family} {H : Finset ι} {g v : ι}
    (hv : v ∈ A.tailAt F H g) : ∃ i, g ∈ F.seg i ∧ v ∈ F.seg i ∧ v ∉ H := by
  classical
  unfold tailAt at hv
  split_ifs at hv with h
  · exact ⟨h.choose, h.choose_spec, (Finset.mem_filter.mp hv).1, (Finset.mem_filter.mp hv).2⟩
  · simp at hv

lemma tailAt_outside {F : A.segments.Family} {H : Finset ι} {g v : ι}
    (hv : v ∈ A.tailAt F H g) : v ∉ H := (A.tailAt_mem hv).choose_spec.2.2

lemma tailAt_cone {F : A.segments.Family} {H : Finset ι} {g v : ι}
    (hg : A.Gate (H : Set ι) g) (hv : v ∈ A.tailAt F H g) : g ≤ v := by
  obtain ⟨i,hgi,hvi,hvH⟩ := A.tailAt_mem hv
  rcases A.interval_chain (F.allowed i) g hgi v hvi with h | h
  · exact h
  · by_contra hn
    have hvne : v ≠ g := fun he => hn (he ▸ le_rfl)
    exact hvH (hg.2 v (lt_of_le_of_ne h hvne))

lemma gate_on_nonzero_segment {H K : Finset ι} (hH : A.Ancestral (H : Set ι))
    (hK : A.Ancestral (K : Set ι)) (F : A.segments.Family)
    (hFK : ∀ i, F.seg i ⊆ K) (p : ι →₀ ℝ) (hp : ∀ v, v ∉ H → p v = 0)
    (i : Fin F.n) (hi : (∑ v ∈ F.seg i, p v) ≠ 0) {v : ι}
    (hvi : v ∈ F.seg i) (hvH : v ∉ H) :
    ∃ g ∈ K, A.Gate (H : Set ι) g ∧ g ∈ F.seg i := by
  classical
  obtain ⟨w, hwi, hpw⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
  have hwH : w ∈ H := by by_contra hn; exact hpw (hp w hn)
  have hfH : A.first F i ∈ H := hH (A.first_le_of_mem F i hwi) hwH
  obtain ⟨g,hgK,hg,hgv⟩ := A.exists_gate_le hK (hFK i hvi) hvH
  obtain ⟨b,hfb,hm⟩ := A.first_spec F i
  have hfg : A.first F i ≤ g := by
    rcases A.predecessors_total (A.first_le_of_mem F i hvi) hgv with h | h
    · exact h
    · exact False.elim (hg.1 (hH h hfH))
  exact ⟨g,hgK,hg,(hm g).mpr ⟨hfg,hgv.trans ((hm v).mp hvi).2⟩⟩

lemma mem_gateSet {H K : Finset ι} {g : ι} :
    g ∈ A.gateSet H K ↔ g ∈ K ∧ A.Gate (H : Set ι) g := Finset.mem_filter

/-- Replacement coefficients have no wholly exterior contribution. Their entire
    tail is the sum of their crossing tails at the finitely represented gates. -/
lemma replaced_tail_eq {H K : Finset ι} (hH : A.Ancestral (H : Set ι))
    (hK : A.Ancestral (K : Set ι)) (F : A.segments.Family)
    (hFK : ∀ i, F.seg i ⊆ K) (p : ι →₀ ℝ) (hp : ∀ v, v ∉ H → p v = 0) :
    A.segments.tailDual H (A.segments.combine F.seg (fun i => ∑ v ∈ F.seg i, p v)) =
      A.segments.combine (fun g : A.gateSet H K => A.tailAt F H g.val)
        (fun g : A.gateSet H K => A.boundaryCoeff F p g.val) := by
  classical
  apply A.segments.dual_ext
  intro v
  rw [SegmentSystem.tailDual_apply, sub_apply, SegmentSystem.headDual_unit]
  by_cases hvH : v ∈ H
  · rw [ite_eq_left hvH, sub_self, SegmentSystem.combine_unit]
    symm
    apply Finset.sum_eq_zero
    intro g _
    rw [ite_eq_right (fun hv => A.tailAt_outside hv hvH)]
  rw [ite_eq_right hvH, sub_zero]
  by_cases hhas : ∃ i, v ∈ F.seg i
  · obtain ⟨i,hvi⟩ := hhas
    rw [A.segments.combine_unit_of_mem F _ i hvi, SegmentSystem.combine_unit]
    by_cases hi : (∑ w ∈ F.seg i, p w) = 0
    · rw [hi]
      symm
      apply Finset.sum_eq_zero
      intro g _
      split_ifs with hv
      · obtain ⟨j,hgj,hvj,_⟩ := A.tailAt_mem hv
        have hji : j = i := by
          by_contra hn
          exact Finset.disjoint_left.mp (F.disjoint hn) hvj hvi
        subst j
        rwa [A.boundaryCoeff_eq F p i hgj]
      · rfl
    obtain ⟨g,hgK,hg,hgi⟩ := A.gate_on_nonzero_segment hH hK F hFK p hp i hi hvi hvH
    let g' : A.gateSet H K := ⟨g, A.mem_gateSet.mpr ⟨hgK,hg⟩⟩
    have hvJ : v ∈ A.tailAt F H g := by
      rw [A.tailAt_eq F H i hgi]
      exact Finset.mem_filter.mpr ⟨hvi,hvH⟩
    rw [Finset.sum_eq_single g']
    · rw [ite_eq_left hvJ, A.boundaryCoeff_eq F p i hgi]
    · intro h _ hh
      rw [ite_eq_right]
      intro hv
      have he : h.val = g := A.gates_eq_of_common_upper
        (A.mem_gateSet.mp h.property).2 hg
        (A.tailAt_cone (A.mem_gateSet.mp h.property).2 hv) (A.tailAt_cone hg hvJ)
      exact hh (Subtype.ext he)
    · simp
  · have hn : ∀ i, v ∉ F.seg i := by simpa only [not_exists] using hhas
    rw [SegmentSystem.combine_unit, SegmentSystem.combine_unit]
    have hz : (∑ i, if v ∈ F.seg i then (∑ w ∈ F.seg i,p w) else 0) = 0 := by simp [hn]
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro g _
    rw [ite_eq_right]
    intro hv
    obtain ⟨i,_,hvi,_⟩ := A.tailAt_mem hv
    exact hn i hvi

end Ancestry

end DiamondDistortion

end

end OAI

-- ---- platform node ----
open OAI OAI.DiamondDistortion OAI.DiamondDistortion.Ancestry
open scoped BigOperators Classical Topology
open Set
open scoped Classical
attribute [local instance] OAI.DiamondDistortion.Ancestry.instPartialOrder


theorem solution : type_of% @_root_.OAI.DiamondDistortion.Ancestry.replaced_tail_eq := @_root_.OAI.DiamondDistortion.Ancestry.replaced_tail_eq
