-- Prove2me | solution 1 for OAI.CriticalZ3.boundary_eq_union_quarterFace
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:29:39.407408+00:00
-- url     : https://prove2.me/submissions/282ef7c0-f310-4582-b322-422ac6cffce4

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces

open OAI OAI.CriticalZ3
universe uE uI uV uW
open MeasureTheory ProbabilityTheory Classical
open Classical
theorem qf_sub (c : Vertex) (n : ℕ) (f : FaceIndex) :
    QuarterFace c n f ⊆ cubeBoundary c n := by
  intro x ⟨h1, h2⟩
  refine ⟨mem_cube.mpr (fun i => ?_), f.1, ?_⟩
  · by_cases hi : i = f.1
    · subst hi; split_ifs at h1 <;> constructor <;> omega
    · have := h2 i hi; split_ifs at this <;> constructor <;> omega
  · split_ifs at h1 <;> omega

theorem solution (c : Vertex) (n : ℕ) :
    cubeBoundary c n = ⋃ f : FaceIndex, QuarterFace c n f := by
  apply Set.Subset.antisymm
  · rintro x ⟨hc, i, hi⟩
    have hc' := mem_cube.mp hc
    rw [Set.mem_iUnion]
    refine ⟨(i, fun j => if j = i then decide (x i = c i + (n : ℤ)) else decide (c j ≤ x j)), ?_, ?_⟩
    · simp only [if_true]
      by_cases h : x i = c i + (n : ℤ) <;> simp [h] <;> omega
    · intro j hj
      have := hc' j
      simp only [hj, if_false]
      by_cases h : c j ≤ x j <;> simp [h] <;> omega
  · exact Set.iUnion_subset (fun f => qf_sub c n f)

