-- Prove2me | solution 1 for OAI.DiamondDistortion.Ancestry.localize_family_energy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:51:46.625089+00:00
-- url     : https://prove2.me/submissions/d1d3e105-057c-417c-aa68-d7fb57dd3b8c

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/Ancestry.lean:L694-L763
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.Ancestry.localize_family_energy. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
import Theorems.Thm_OAI_DiamondDistortion_Ancestry_segment_filter_head

-- ---- from OAI.Analysis.DiamondDistortion.Ancestry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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
/-- Restricting any test family to a finite ancestral set gives one of the
    finitely many local families, with exactly the same energy for supported tests. -/
lemma localize_family_energy {K : Finset ι} (hK : A.Ancestral (K : Set ι))
    (F : A.segments.Family) (p : ι →₀ ℝ) (hp : ∀ v, v ∉ K → p v = 0) :
    ∃ G : A.segments.LocalFamily K,
      (∑ i, (∑ v ∈ F.seg i, p v) ^ 2) =
        ∑ S : A.segments.LocalIndex G, (∑ v ∈ S.val, p v) ^ 2 := by
  classical
  let P : Fin F.n → Prop := fun i => ((F.seg i).filter (· ∈ K)).Nonempty
  let I := {i : Fin F.n // P i}
  let f : I → Finset ι := fun i => (F.seg i.val).filter (· ∈ K)
  have hf : Function.Injective f := by
    intro i j he
    apply Subtype.ext
    by_contra hne
    obtain ⟨v, hv⟩ := i.property
    have hvj : v ∈ f j := by rw [← he]; exact hv
    exact Finset.disjoint_left.mp (F.disjoint hne)
      (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hvj).1
  let Gset := Finset.univ.image f
  have hGK : Gset ∈ K.powerset.powerset := by
    apply Finset.mem_powerset.mpr
    intro S hS
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hS
    apply Finset.mem_powerset.mpr
    intro v hv
    exact (Finset.mem_filter.mp hv).2
  have hGa : ∀ S ∈ Gset, A.segments.IsSegment S := by
    intro S hS
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hS
    convert A.segment_filter_head (F.allowed i.val) hK (by
      have hi := i.property
      change ((F.seg i.val).filter (fun v => v ∈ K)).Nonempty at hi
      simpa only [Finset.filter_nonempty_iff, Finset.mem_coe] using hi) using 1
    ext v
    simp only [f, Finset.mem_filter, Finset.mem_coe]

  have hGd : (Gset : Set (Finset ι)).Pairwise Disjoint := by
    intro S hS U hU hSU
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hU
    have hij : i.val ≠ j.val := fun h => hSU (congrArg f (Subtype.ext h))
    exact (F.disjoint hij).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  let G : A.segments.LocalFamily K := ⟨Gset, hGK, hGa, hGd⟩
  refine ⟨G, ?_⟩
  have hsum (i : Fin F.n) : (∑ v ∈ F.seg i, p v) =
      ∑ v ∈ (F.seg i).filter (· ∈ K), p v := by
    symm
    apply Finset.sum_filter_of_ne
    intro v _ hv
    by_contra hn
    exact hv (hp v hn)
  have hzero : (∑ i : {i : Fin F.n // ¬ P i},
      (∑ v ∈ (F.seg i.val).filter (· ∈ K), p v) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hi : (F.seg i.val).filter (· ∈ K) = ∅ := Finset.not_nonempty_iff_eq_empty.mp i.property
    rw [hi]
    simp
  have he := Fintype.sum_subtype_add_sum_subtype P
    (fun i => (∑ v ∈ (F.seg i).filter (· ∈ K), p v) ^ 2)
  rw [hzero, add_zero] at he
  simp_rw [hsum]
  rw [← he]
  change (∑ i : I, (∑ v ∈ f i, p v) ^ 2) =
    ∑ S : ↥Gset, (∑ v ∈ S.val, p v) ^ 2
  calc
    _ = ∑ S ∈ Gset, (∑ v ∈ S, p v) ^ 2 :=
      (Finset.sum_image (fun _ _ _ _ h => hf h)).symm
    _ = _ := (Finset.sum_coe_sort Gset (fun S => (∑ v ∈ S, p v) ^ 2)).symm

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


theorem solution : type_of% @_root_.OAI.DiamondDistortion.Ancestry.localize_family_energy := @_root_.OAI.DiamondDistortion.Ancestry.localize_family_energy
