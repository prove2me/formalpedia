-- Prove2me | solution 1 for OAI.CriticalZ3.nearestNeighbor_exit_boundary
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:33:18.55004+00:00
-- url     : https://prove2.me/submissions/e558f5c4-e68e-46fa-8b82-a4066b4c8013

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic

open OAI OAI.CriticalZ3
universe uE uOmega uV
open MeasureTheory ProbabilityTheory
open Filter
open scoped Topology


theorem solution {c x y : Vertex} {n : ℕ}
    (hx : x ∈ cube c n) (hy : y ∉ cube c n) (hxy : NearestNeighbor x y) :
    x ∈ cubeBoundary c n := by
  refine ⟨hx, ?_⟩
  have hx' := mem_cube.mp hx
  by_contra hne
  push_neg at hne
  apply hy
  rw [mem_cube]
  intro j
  obtain ⟨i, h | h⟩ := hxy
  · have e := congrFun h j
    have := hx' j; have := hne j
    have hi := hx' i; have hni := hne i
    have ei := congrFun h i
    simp only [step] at e ei
    by_cases hij : i = j
    · subst hij; simp at e; constructor <;> omega
    · simp [hij] at e; constructor <;> omega
  · have e := congrFun h j
    have := hx' j; have := hne j
    simp only [step] at e
    by_cases hij : i = j
    · subst hij; simp at e; constructor <;> omega
    · simp [hij] at e; constructor <;> omega

