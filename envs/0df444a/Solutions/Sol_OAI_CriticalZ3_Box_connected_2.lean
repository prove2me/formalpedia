-- Prove2me | solution 2 for OAI.CriticalZ3.Box.connected
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:24:10.529869+00:00
-- url     : https://prove2.me/submissions/b00badbc-2923-4954-aa28-d900188abcfc

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/BoxGeometry.lean:L376-L397
-- (upload_full_project.md Phase 4): solution for node OAI.CriticalZ3.Box.connected. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry

-- ---- from OAI.Probability.CriticalZ3.BoxGeometry ----
namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3

open Classical

namespace Box

theorem within_symm (B : Box) {x y : Vertex} (h : B.Within x y) : B.Within y x := by
  obtain ⟨⟨i,hi⟩,hx,hy⟩ := h
  exact ⟨⟨i,hi.symm⟩,hy,hx⟩

theorem within_path_symm (B : Box) {x y : Vertex}
    (h : Relation.ReflTransGen B.Within x y) : Relation.ReflTransGen B.Within y x := by
  induction h with
  | refl => exact .refl
  | tail _ hab ih => exact .head (B.within_symm hab) ih

theorem line_step (x : Vertex) (i : Fin 3) (n : ℤ) :
    Function.update x i (n+1) = step (Function.update x i n) i := by
  funext j
  by_cases hj : j = i
  · subst j; simp [step]
  · simp [step,hj,Ne.symm hj]

theorem line_contains (B : Box) {x : Vertex} (hx : B.Contains x) (i : Fin 3)
    (n : ℤ) (hn : B.lower i ≤ n ∧ n ≤ B.upper i) : B.Contains (Function.update x i n) := by
  intro j
  by_cases hj : j = i
  · subst j; simpa using hn
  · simpa [Function.update_of_ne hj] using hx j

theorem line_path_le (B : Box) {x : Vertex} (hx : B.Contains x) (i : Fin 3)
    {a b : ℤ} (ha : B.lower i ≤ a) (hb : b ≤ B.upper i) (hab : a ≤ b) :
    Relation.ReflTransGen B.Within (Function.update x i a) (Function.update x i b) := by
  have hh (n : ℤ) (han : a ≤ n) : n ≤ b →
      Relation.ReflTransGen B.Within (Function.update x i a) (Function.update x i n) := by
    induction n,han using Int.leInduction with
    | base => intro _; exact .refl
    | succ n han ih =>
      intro hn
      apply (ih (by omega)).tail
      exact ⟨⟨i,Or.inl (line_step x i n)⟩,
        B.line_contains hx i n ⟨by omega,by omega⟩,
        B.line_contains hx i (n+1) ⟨by omega,by omega⟩⟩
  exact hh b hab le_rfl

theorem line_path (B : Box) {x : Vertex} (hx : B.Contains x) (i : Fin 3)
    {b : ℤ} (hb : B.lower i ≤ b ∧ b ≤ B.upper i) :
    Relation.ReflTransGen B.Within x (Function.update x i b) := by
  have hx' := hx i
  by_cases h : x i ≤ b
  · simpa using B.line_path_le hx i hx'.1 hb.2 h
  · apply B.within_path_symm
    simpa using B.line_path_le hx i hb.1 hx'.2 (le_of_not_ge h)

/-- Every nonempty integer rectangle is nearest-neighbor connected internally. -/
theorem connected (B : Box) {x y : Vertex} (hx : B.Contains x) (hy : B.Contains y) :
    Relation.ReflTransGen B.Within x y := by
  let patch (s : Finset (Fin 3)) : Vertex := fun i => if i ∈ s then y i else x i
  have hp (s : Finset (Fin 3)) : B.Contains (patch s) := by
    intro i
    by_cases hi : i ∈ s
    · simpa [patch,hi] using hy i
    · simpa [patch,hi] using hx i
  have hc (s : Finset (Fin 3)) : Relation.ReflTransGen B.Within x (patch s) := by
    induction s using Finset.induction_on with
    | empty => simpa only [patch,Finset.notMem_empty,ite_false] using
        (Relation.ReflTransGen.refl : Relation.ReflTransGen B.Within x x)
    | @insert i s hi ih =>
      have he : patch (insert i s) = Function.update (patch s) i (y i) := by
        funext j
        by_cases hj : j = i
        · subst j; simp [patch]
        · simp [patch,hj]
      rw [he]
      exact ih.trans (B.line_path (hp s) i (hy i))
  simpa only [patch,Finset.mem_univ,ite_true] using hc Finset.univ

end Box
end CriticalZ3

end OAI

-- ---- platform node ----
open OAI OAI.CriticalZ3 OAI.CriticalZ3.Box
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open Classical


theorem solution : type_of% @_root_.OAI.CriticalZ3.Box.connected := @_root_.OAI.CriticalZ3.Box.connected
