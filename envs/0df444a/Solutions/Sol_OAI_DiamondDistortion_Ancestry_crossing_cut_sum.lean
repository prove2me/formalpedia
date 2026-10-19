-- Prove2me | solution 1 for OAI.DiamondDistortion.Ancestry.crossing_cut_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:36:52.869545+00:00
-- url     : https://prove2.me/submissions/dd069292-85b8-4721-acee-179b247f04cb

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/Ancestry.lean:L223-L257
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.Ancestry.crossing_cut_sum. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry

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
lemma interval_chain {S : Finset ι} (hS : A.segments.IsSegment S) :
    ∀ a ∈ S, ∀ b ∈ S, a ≤ b ∨ b ≤ a := by
  obtain ⟨l, r, _, hmem⟩ := hS
  intro a ha b hb
  exact A.predecessors_total ((hmem a).mp ha).2 ((hmem b).mp hb).2

lemma first_spec (F : A.segments.Family) (i : Fin F.n) :
    ∃ b, A.first F i ≤ b ∧ ∀ v, v ∈ F.seg i ↔ A.first F i ≤ v ∧ v ≤ b :=
  Classical.choose_spec (F.allowed i)

/-- Two heads through a common exterior vertex are nested; cutting the longer
    at the shorter's first vertex preserves exactly the shorter head sum. -/
lemma crossing_cut_sum {H : Set ι} (hH : A.Ancestral H) (p : ι →₀ ℝ)
    (hp : ∀ v, v ∉ H → p v = 0) (F G : A.segments.Family)
    (i : Fin F.n) (j : Fin G.n) {g : ι} (hg : g ∉ H)
    (hgF : g ∈ F.seg i) (hgG : g ∈ G.seg j)
    (hfirst : A.first F i ≤ A.first G j) :
    (∑ v ∈ (F.seg i).filter (fun v => A.first G j ≤ v), p v) =
      ∑ v ∈ G.seg j, p v := by
  classical
  obtain ⟨b, hfb, hFm⟩ := A.first_spec F i
  obtain ⟨d, hgd, hGm⟩ := A.first_spec G j
  have hhead : ∀ S, A.segments.IsSegment S → g ∈ S → ∀ v ∈ S, v ∈ H → v ≤ g := by
    intro S hS hgS v hv hvH
    rcases A.interval_chain hS v hv g hgS with h | h
    · exact h
    · exact False.elim (hg (hH h hvH))
  have he : ((F.seg i).filter (fun v => A.first G j ≤ v)).filter (· ∈ H) =
      (G.seg j).filter (· ∈ H) := by
    ext v
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hvF, hvfirst⟩, hvH⟩
      refine ⟨(hGm v).mpr ⟨hvfirst, ?_⟩, hvH⟩
      exact (hhead _ (F.allowed i) hgF v hvF hvH).trans ((hGm g).mp hgG).2
    · rintro ⟨hvG, hvH⟩
      have hvg := hhead _ (G.allowed j) hgG v hvG hvH
      exact ⟨⟨(hFm v).mpr ⟨hfirst.trans ((hGm v).mp hvG).1,
        hvg.trans ((hFm g).mp hgF).2⟩, ((hGm v).mp hvG).1⟩, hvH⟩
  have hf (S : Finset ι) : (∑ v ∈ S.filter (· ∈ H), p v) = ∑ v ∈ S, p v := by
    apply Finset.sum_filter_of_ne
    intro v _ hpv
    by_contra hvH
    exact hpv (hp v hvH)
  rw [← hf ((F.seg i).filter (fun v => A.first G j ≤ v)), he, hf]

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


theorem solution : type_of% @_root_.OAI.DiamondDistortion.Ancestry.crossing_cut_sum := @_root_.OAI.DiamondDistortion.Ancestry.crossing_cut_sum
