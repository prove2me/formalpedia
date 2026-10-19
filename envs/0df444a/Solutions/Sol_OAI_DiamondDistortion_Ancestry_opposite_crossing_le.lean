-- Prove2me | solution 1 for OAI.DiamondDistortion.Ancestry.opposite_crossing_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:45:35.106164+00:00
-- url     : https://prove2.me/submissions/c219eb21-cba2-4983-8991-9e1203bbbc2f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/Ancestry.lean:L403-L467
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.Ancestry.opposite_crossing_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
import Theorems.Thm_OAI_DiamondDistortion_Ancestry_opposite_matching_le

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

lemma gates_eq_of_le {H : Set ι} {g h : ι} (hg : A.Gate H g)
    (hh : A.Gate H h) (hgh : g ≤ h) : g = h := by
  by_contra hne
  exact hg.1 (hh.2 g (lt_of_le_of_ne hgh hne))

lemma gate_unique_in_segment {H : Set ι} {S : Finset ι}
    (hS : A.segments.IsSegment S) {g h : ι} (hg : A.Gate H g)
    (hh : A.Gate H h) (hgS : g ∈ S) (hhS : h ∈ S) : g = h := by
  rcases A.interval_chain hS g hgS h hhS with h | h
  · exact A.gates_eq_of_le hg hh h
  · exact (A.gates_eq_of_le hh hg h).symm

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

lemma boundaryCoeff_nonzero_mem (F : A.segments.Family) (p : ι →₀ ℝ)
    {g : ι} (h : A.boundaryCoeff F p g ≠ 0) : ∃ i, g ∈ F.seg i := by
  classical
  by_contra hn
  have hm : ∀ i, g ∉ F.seg i := by simpa using hn
  exact h (by simp [boundaryCoeff, hm])

/-- Exact two-family opposite-crossing estimate, written without a sign-filter
    so that it can be averaged over independent finite endpoint laws. -/
lemma opposite_crossing_le {κ : Type*} [Fintype κ]
    {H : Set ι} (hH : A.Ancestral H) (p : ι →₀ ℝ)
    (hp : ∀ v, v ∉ H → p v = 0) (F G : A.segments.Family)
    (gate : κ ↪ ι) (hgate : ∀ a, A.Gate H (gate a)) :
    (∑ a, (|A.boundaryCoeff F p (gate a)| * |A.boundaryCoeff G p (gate a)| -
      A.boundaryCoeff F p (gate a) * A.boundaryCoeff G p (gate a))) ≤
      ((A.segments.primalSeminorm p) ^ 2 - ∑ i, (∑ v ∈ F.seg i, p v) ^ 2) +
      ((A.segments.primalSeminorm p) ^ 2 - ∑ j, (∑ v ∈ G.seg j, p v) ^ 2) := by
  classical
  let P : κ → Prop := fun a => A.boundaryCoeff F p (gate a) *
    A.boundaryCoeff G p (gate a) < 0
  let M := {a : κ // P a}
  have hnF (a : M) : A.boundaryCoeff F p (gate a.val) ≠ 0 := by
    intro he
    have := a.property
    change A.boundaryCoeff F p (gate a.val) * A.boundaryCoeff G p (gate a.val) < 0 at this
    simp [he] at this
  have hnG (a : M) : A.boundaryCoeff G p (gate a.val) ≠ 0 := by
    intro he
    have := a.property
    change A.boundaryCoeff F p (gate a.val) * A.boundaryCoeff G p (gate a.val) < 0 at this
    simp [he] at this
  choose iF hiF using fun a : M => A.boundaryCoeff_nonzero_mem F p (hnF a)
  choose iG hiG using fun a : M => A.boundaryCoeff_nonzero_mem G p (hnG a)
  have hiFinj : Function.Injective iF := by
    intro a b hab
    apply Subtype.ext
    apply gate.injective
    exact A.gate_unique_in_segment (F.allowed (iF a)) (hgate a.val) (hgate b.val)
      (hiF a) (by rw [hab]; exact hiF b)
  have hiGinj : Function.Injective iG := by
    intro a b hab
    apply Subtype.ext
    apply gate.injective
    exact A.gate_unique_in_segment (G.allowed (iG a)) (hgate a.val) (hgate b.val)
      (hiG a) (by rw [hab]; exact hiG b)
  have hbF (a : M) := A.boundaryCoeff_eq F p (iF a) (hiF a)
  have hbG (a : M) := A.boundaryCoeff_eq G p (iG a) (hiG a)
  have hb := A.opposite_matching_le hH p hp F G ⟨iF, hiFinj⟩ ⟨iG, hiGinj⟩
    (fun a => gate a.val) (fun a => (hgate a.val).1) hiF hiG (by
      intro a
      change (∑ v ∈ F.seg (iF a), p v) * (∑ v ∈ G.seg (iG a), p v) < 0
      rw [← hbF, ← hbG]
      exact a.property)
  simp only [Function.Embedding.coeFn_mk, ← hbF, ← hbG] at hb
  let f : κ → ℝ := fun a => |A.boundaryCoeff F p (gate a)| *
    |A.boundaryCoeff G p (gate a)| - A.boundaryCoeff F p (gate a) * A.boundaryCoeff G p (gate a)
  have hzero : (∑ a : {a : κ // ¬ P a}, f a.val) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    dsimp [f]
    rw [← abs_mul, abs_of_nonneg (le_of_not_gt a.property), sub_self]
  have heq : (∑ a : M, f a.val) =
      2 * ∑ a : M, |A.boundaryCoeff F p (gate a.val) * A.boundaryCoeff G p (gate a.val)| := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    dsimp [f]
    rw [← abs_mul, abs_of_neg a.property]
    ring
  have hs := Fintype.sum_subtype_add_sum_subtype P f
  rw [hzero, add_zero, heq] at hs
  simpa only [hs] using hb

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


theorem solution : type_of% @_root_.OAI.DiamondDistortion.Ancestry.opposite_crossing_le := @_root_.OAI.DiamondDistortion.Ancestry.opposite_crossing_le
