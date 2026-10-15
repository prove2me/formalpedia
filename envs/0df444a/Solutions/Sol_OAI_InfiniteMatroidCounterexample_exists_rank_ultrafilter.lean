-- Prove2me | solution 1 for OAI.InfiniteMatroidCounterexample.exists_rank_ultrafilter
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T03:47:35.110991+00:00
-- url     : https://prove2.me/submissions/0efbd1c0-88a7-43bc-bf55-3b584931cd2f

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/InfiniteMatroid/Ideals.lean:L107-L161
-- (upload_full_project.md Phase 4): solution for node OAI.InfiniteMatroidCounterexample.exists_rank_ultrafilter. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_InfiniteMatroid
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Cardinality
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Ideals

-- ---- from OAI.Combinatorics.InfiniteMatroid.Ideals ----
namespace OAI

section

open Set Filter
open scoped symmDiff

namespace InfiniteMatroidCounterexample

namespace SubsetIdeal
variable {α : Type*} (K : SubsetIdeal α)

lemma finite_sUnion {S : Set (Set α)} (hS : S.Finite) (h : ∀ X ∈ S, K.small X) :
    K.small (⋃₀ S) := by
  induction S, hS using Set.Finite.induction_on with
  | empty => simpa using K.empty
  | @insert X S hn hS ih =>
    rw [sUnion_insert]
    exact K.union (h X (mem_insert _ _)) (ih (fun Y hY ↦ h Y (mem_insert_of_mem _ hY)))

lemma positive_nonempty {X : Set α} (h : ¬ K.small X) : X.Nonempty := by
  by_contra hn
  exact h ((not_nonempty_iff_eq_empty.mp hn).symm ▸ K.empty)

lemma remove_small {X N : Set α} (hX : ¬ K.small X) (hN : K.small N) :
    ¬ K.small (X \ N) := by
  intro h
  apply hX
  exact K.mono (K.union hN h) (by intro x hx; by_cases hn : x ∈ N; exact Or.inl hn; exact Or.inr ⟨hx, hn⟩)

end SubsetIdeal

lemma forbidden_finite_avoidance {α ι : Type*} (K : SubsetIdeal α) (G : ι → Set α)
    (hpattern : ∀ F H : Finset ι, Disjoint F H → ¬ K.small (columnPattern G F H))
    {N : Set α} (hN : K.small N) (F : Finset ι) {Z : Set (Set α)}
    (hZ : Z.Finite) (hforbid : ∀ z ∈ Z, Forbidden K G z) :
    ({x | (∀ t ∈ F, x ∈ G t)} \ (N ∪ ⋃₀ Z)).Nonempty := by
  classical
  have hchoose : ∀ z : Z, ∃ t, t ∉ F ∧ K.ModSubset z.val (G t) := by
    intro z
    obtain ⟨t, ht, hnot⟩ := (hforbid z.val z.property).exists_notMem_finset F
    exact ⟨t, hnot, ht⟩
  choose t htF htK using hchoose
  let H : Finset ι := hZ.toFinset.attach.image (fun z ↦ t ⟨z.val, hZ.mem_toFinset.mp z.property⟩)
  have hH : ∀ z : Z, t z ∈ H := by
    intro z
    apply Finset.mem_image.mpr
    exact ⟨⟨z.val, hZ.mem_toFinset.mpr z.property⟩, by simp, rfl⟩
  have hdisj : Disjoint F H := by
    apply Finset.disjoint_left.mpr
    intro i hiF hiH
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hiH
    exact htF ⟨z.val, hZ.mem_toFinset.mp z.property⟩ hiF
  let P := columnPattern G F H
  have hp : ¬ K.small P := hpattern F H hdisj
  have hpz : ∀ z ∈ Z, K.small (P ∩ z) := by
    intro z hz
    apply K.mono (htK ⟨z, hz⟩)
    intro x hx
    exact ⟨hx.2, hx.1.2 _ (hH ⟨z, hz⟩)⟩
  have hsmall : K.small (N ∪ ⋃₀ ((fun z ↦ P ∩ z) '' Z)) :=
    K.union hN (K.finite_sUnion (hZ.image _) (by rintro _ ⟨z, hz, rfl⟩; exact hpz z hz))
  obtain ⟨x, hxP, hxnot⟩ := K.positive_nonempty (K.remove_small hp hsmall)
  refine ⟨x, hxP.1, ?_⟩
  rintro (hxN | hxZ)
  · exact hxnot (Or.inl hxN)
  · obtain ⟨z, hz, hxz⟩ := mem_sUnion.mp hxZ
    exact hxnot (Or.inr (mem_sUnion.mpr ⟨P ∩ z, mem_image_of_mem _ hz, hxP, hxz⟩))

/-- The finite-intersection argument produces the required ultrafilter;
no countable completeness or continuum regularity is used. -/
lemma exists_rank_ultrafilter {α ι : Type*} (K : SubsetIdeal α) (G : ι → Set α)
    (hpattern : ∀ F H : Finset ι, Disjoint F H → ¬ K.small (columnPattern G F H)) :
    ∃ U : Ultrafilter α,
      (∀ N, K.small N → N ∉ U) ∧ (∀ t, G t ∈ U) ∧
      (∀ X, X ∈ U → {t | K.ModSubset X (G t)}.Finite) := by
  classical
  let S : Set (Set α) := {s | (∃ N, K.small N ∧ s = Nᶜ) ∨
    (∃ t, s = G t) ∨ (∃ Z, Forbidden K G Z ∧ s = Zᶜ)}
  have hFIP : ∀ T : Finset (Set α), (↑T : Set (Set α)) ⊆ S → (⋂₀ (↑T : Set (Set α))).Nonempty := by
    intro T hTS
    let Ns := {s ∈ T | ∃ N, K.small N ∧ s = Nᶜ}
    let Gs := {s ∈ T | ∃ t, s = G t}
    let Zs := {s ∈ T | ∃ Z, Forbidden K G Z ∧ s = Zᶜ}
    have hNs : ∀ s ∈ Ns, K.small sᶜ := by
      intro s hs
      obtain ⟨N, hN, rfl⟩ := (Finset.mem_filter.mp hs).2
      simpa using hN
    have hGs : ∀ s : {s // s ∈ Gs}, ∃ t, s.val = G t := fun s ↦ (Finset.mem_filter.mp s.property).2
    choose g hg using hGs
    let F : Finset ι := Gs.attach.image g
    let N : Set α := ⋃₀ ((fun s : Set α ↦ sᶜ) '' (↑Ns : Set (Set α)))
    let Z : Set (Set α) := (fun s : Set α ↦ sᶜ) '' (↑Zs : Set (Set α))
    have hN : K.small N := K.finite_sUnion (Ns.finite_toSet.image _)
      (by rintro _ ⟨s, hs, rfl⟩; exact hNs s hs)
    have hZ : Z.Finite := Zs.finite_toSet.image _
    have hforbid : ∀ z ∈ Z, Forbidden K G z := by
      rintro z ⟨s, hs, rfl⟩
      obtain ⟨z, hz, rfl⟩ := (Finset.mem_filter.mp hs).2
      simpa using hz
    obtain ⟨x, hxG, hxNZ⟩ := forbidden_finite_avoidance K G hpattern hN F hZ hforbid
    refine ⟨x, mem_sInter.mpr ?_⟩
    intro s hs
    rcases hTS hs with hsmall | hcol | hforb
    · have hNs' : s ∈ Ns := Finset.mem_filter.mpr ⟨hs, hsmall⟩
      by_contra hxs
      exact hxNZ (Or.inl (mem_sUnion.mpr ⟨sᶜ, mem_image_of_mem _ hNs', hxs⟩))
    · have hGs' : s ∈ Gs := Finset.mem_filter.mpr ⟨hs, hcol⟩
      have heq : s = G (g ⟨s, hGs'⟩) := hg ⟨s, hGs'⟩
      rw [heq]
      exact hxG _ (Finset.mem_image.mpr ⟨⟨s, hGs'⟩, by simp, rfl⟩)
    · have hZs' : s ∈ Zs := Finset.mem_filter.mpr ⟨hs, hforb⟩
      by_contra hxs
      exact hxNZ (Or.inr (mem_sUnion.mpr ⟨sᶜ, mem_image_of_mem _ hZs', hxs⟩))
  obtain ⟨U, hU⟩ := Ultrafilter.exists_ultrafilter_of_finite_inter_nonempty S hFIP
  refine ⟨U, ?_, ?_, ?_⟩
  · intro N hN
    exact Ultrafilter.compl_mem_iff_notMem.mp (hU (Or.inl ⟨N, hN, rfl⟩))
  · intro t
    exact hU (Or.inr (Or.inl ⟨t, rfl⟩))
  · intro X hX
    by_contra hfin
    have hc : Xᶜ ∈ U := hU (Or.inr (Or.inr ⟨X, hfin, rfl⟩))
    exact (Ultrafilter.compl_mem_iff_notMem.mp hc) hX

end InfiniteMatroidCounterexample
end

end OAI

-- ---- platform node ----
open OAI OAI.InfiniteMatroidCounterexample
open Set Filter
open scoped symmDiff


theorem solution : type_of% @_root_.OAI.InfiniteMatroidCounterexample.exists_rank_ultrafilter := @_root_.OAI.InfiniteMatroidCounterexample.exists_rank_ultrafilter
