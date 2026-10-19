-- Prove2me | solution 2 for OAI.CriticalZ3.nearestNeighbor_exit_boundary
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:13:38.348689+00:00
-- url     : https://prove2.me/submissions/86ff778c-e3e3-43c4-9e90-0bfb59bbc284

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/Basic.lean:L588-L615
-- (upload_full_project.md Phase 4): solution for node OAI.CriticalZ3.nearestNeighbor_exit_boundary. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic

-- ---- from OAI.Probability.CriticalZ3.Basic ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uE uOmega uV

-- [generator] trimmed: open MeasureTheory ProbabilityTheory
open _root_.MeasureTheory ProbabilityTheory

namespace CriticalZ3

/-! Finite alterations, tail invariance, and the infinite seed limit. -/

open Filter
open scoped Topology

theorem nearestNeighbor_exit_boundary {c x y : Vertex} {n : ℕ}
    (hx : x ∈ cube c n) (hy : y ∉ cube c n) (hxy : NearestNeighbor x y) :
    x ∈ cubeBoundary c n := by
  refine ⟨hx,?_⟩
  rw [mem_cube] at hx hy
  push Not at hy
  obtain ⟨i,hi⟩ := hy
  obtain ⟨k,hk | hk⟩ := hxy
  · subst y
    by_cases hki : k = i
    · subst k
      refine ⟨i,Or.inr ?_⟩
      have hxi := hx i
      simp only [step,ite_true] at hi
      omega
    · have hxi := hx i
      simp only [step,ite_eq_right hki,add_zero] at hi
      omega
  · subst x
    by_cases hki : k = i
    · subst k
      refine ⟨i,Or.inl ?_⟩
      have hxi := hx i
      simp only [step,ite_true] at hxi ⊢
      omega
    · have hxi := hx i
      simp only [step,ite_eq_right hki,add_zero] at hxi
      omega

end CriticalZ3

end OAI

-- ---- platform node ----
open OAI OAI.CriticalZ3
open MeasureTheory ProbabilityTheory
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.CriticalZ3.nearestNeighbor_exit_boundary := @_root_.OAI.CriticalZ3.nearestNeighbor_exit_boundary
