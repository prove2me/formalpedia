-- Prove2me | solution 1 for OAI.CriticalZ3.quarterFace_subset_boundary
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:29:46.323118+00:00
-- url     : https://prove2.me/submissions/3eeeb00a-33b6-49b4-a73b-b4c8bfcc79dc

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


theorem solution (c : Vertex) (n : ℕ) (f : FaceIndex) :
    QuarterFace c n f ⊆ cubeBoundary c n := by
  intro x ⟨h1, h2⟩
  refine ⟨mem_cube.mpr (fun i => ?_), f.1, ?_⟩
  · by_cases hi : i = f.1
    · subst hi; split_ifs at h1 <;> constructor <;> omega
    · have := h2 i hi; split_ifs at this <;> constructor <;> omega
  · split_ifs at h1 <;> omega

