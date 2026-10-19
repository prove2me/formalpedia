-- Prove2me | solution 1 for OAI.DiamondDistortion.Ancestry.opposite_matching_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:43:55.394488+00:00
-- url     : https://prove2.me/submissions/afca1e0e-1332-40ed-8ee8-9380c27e6078

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/Ancestry.lean:L315-L379
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.Ancestry.opposite_matching_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
import Theorems.Thm_OAI_DiamondDistortion_Ancestry_crossing_cut_sum
import Theorems.Thm_OAI_DiamondDistortion_Ancestry_matched_split_gain_le

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
lemma first_spec (F : A.segments.Family) (i : Fin F.n) :
    ∃ b, A.first F i ≤ b ∧ ∀ v, v ∈ F.seg i ↔ A.first F i ≤ v ∧ v ≤ b :=
  Classical.choose_spec (F.allowed i)

lemma first_le_of_mem (F : A.segments.Family) (i : Fin F.n) {v : ι}
    (hv : v ∈ F.seg i) : A.first F i ≤ v := by
  obtain ⟨b, _, hm⟩ := A.first_spec F i
  exact ((hm v).mp hv).1

/-- Opposite head sums, matched injectively in both families, spend only the
    combined testing deficits. This is the simultaneous boundary cancellation. -/
lemma opposite_matching_le {κ : Type*} [Fintype κ]
    {H : Set ι} (hH : A.Ancestral H) (p : ι →₀ ℝ)
    (hp : ∀ v, v ∉ H → p v = 0) (F G : A.segments.Family)
    (eF : κ ↪ Fin F.n) (eG : κ ↪ Fin G.n) (g : κ → ι)
    (hgH : ∀ a, g a ∉ H) (hgF : ∀ a, g a ∈ F.seg (eF a))
    (hgG : ∀ a, g a ∈ G.seg (eG a))
    (hopp : ∀ a, (∑ v ∈ F.seg (eF a), p v) * (∑ v ∈ G.seg (eG a), p v) < 0) :
    2 * (∑ a, |(∑ v ∈ F.seg (eF a), p v) * (∑ v ∈ G.seg (eG a), p v)|) ≤
      ((A.segments.primalSeminorm p) ^ 2 - ∑ i, (∑ v ∈ F.seg i, p v) ^ 2) +
      ((A.segments.primalSeminorm p) ^ 2 - ∑ j, (∑ v ∈ G.seg j, p v) ^ 2) := by
  classical
  let P : κ → Prop := fun a => A.first F (eF a) ≤ A.first G (eG a)
  let L := {a : κ // P a}
  let U := {a : κ // ¬ P a}
  let eL : L ↪ Fin F.n := ⟨fun a => eF a.val,
    fun a b h => Subtype.ext (eF.injective h)⟩
  let eU : U ↪ Fin G.n := ⟨fun a => eG a.val,
    fun a b h => Subtype.ext (eG.injective h)⟩
  have hcutL (a : L) :
      (∑ v ∈ (F.seg (eL a)).filter (fun v => A.first G (eG a.val) ≤ v), p v) =
        ∑ v ∈ G.seg (eG a.val), p v :=
    A.crossing_cut_sum hH p hp F G (eF a.val) (eG a.val)
      (hgH a.val) (hgF a.val) (hgG a.val) a.property
  have hcutU (a : U) :
      (∑ v ∈ (G.seg (eU a)).filter (fun v => A.first F (eF a.val) ≤ v), p v) =
        ∑ v ∈ F.seg (eF a.val), p v := by
    have hfirst : A.first G (eG a.val) ≤ A.first F (eF a.val) := by
      rcases A.predecessors_total (A.first_le_of_mem F _ (hgF a.val))
        (A.first_le_of_mem G _ (hgG a.val)) with h | h
      · exact False.elim (a.property h)
      · exact h
    exact A.crossing_cut_sum hH p hp G F (eG a.val) (eF a.val)
      (hgH a.val) (hgG a.val) (hgF a.val) hfirst
  have hF := A.matched_split_gain_le F eL (fun a => A.first G (eG a.val)) p
  have hG := A.matched_split_gain_le G eU (fun a => A.first F (eF a.val)) p
  simp_rw [hcutL] at hF
  simp_rw [hcutU] at hG
  have hL : (∑ a : L, |(∑ v ∈ F.seg (eF a.val), p v) *
      (∑ v ∈ G.seg (eG a.val), p v)|) ≤
      ∑ a : L, ((∑ v ∈ G.seg (eG a.val), p v) ^ 2 -
        (∑ v ∈ F.seg (eL a), p v) * (∑ v ∈ G.seg (eG a.val), p v)) := by
    apply Finset.sum_le_sum
    intro a _
    rw [abs_of_neg (hopp a.val)]
    change -( (∑ v ∈ F.seg (eF a.val), p v) * (∑ v ∈ G.seg (eG a.val), p v)) ≤
      (∑ v ∈ G.seg (eG a.val), p v) ^ 2 -
        (∑ v ∈ F.seg (eF a.val), p v) * (∑ v ∈ G.seg (eG a.val), p v)
    nlinarith [sq_nonneg (∑ v ∈ G.seg (eG a.val), p v)]
  have hU : (∑ a : U, |(∑ v ∈ F.seg (eF a.val), p v) *
      (∑ v ∈ G.seg (eG a.val), p v)|) ≤
      ∑ a : U, ((∑ v ∈ F.seg (eF a.val), p v) ^ 2 -
        (∑ v ∈ G.seg (eU a), p v) * (∑ v ∈ F.seg (eF a.val), p v)) := by
    apply Finset.sum_le_sum
    intro a _
    rw [abs_of_neg (hopp a.val)]
    change -( (∑ v ∈ F.seg (eF a.val), p v) * (∑ v ∈ G.seg (eG a.val), p v)) ≤
      (∑ v ∈ F.seg (eF a.val), p v) ^ 2 -
        (∑ v ∈ G.seg (eG a.val), p v) * (∑ v ∈ F.seg (eF a.val), p v)
    nlinarith [sq_nonneg (∑ v ∈ F.seg (eF a.val), p v)]
  have hsum := Fintype.sum_subtype_add_sum_subtype P (fun a =>
    |(∑ v ∈ F.seg (eF a), p v) * (∑ v ∈ G.seg (eG a), p v)|)
  change (∑ a : L, _) + (∑ a : U, _) = _ at hsum
  linarith

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


theorem solution : type_of% @_root_.OAI.DiamondDistortion.Ancestry.opposite_matching_le := @_root_.OAI.DiamondDistortion.Ancestry.opposite_matching_le
