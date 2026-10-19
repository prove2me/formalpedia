-- Prove2me | solution 1 for OAI.CriticalZ3.Box.exterior_neighbor_unique
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:33:30.249165+00:00
-- url     : https://prove2.me/submissions/9b8ebbd6-045b-48f0-9836-68c1d070c37e

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

open OAI OAI.CriticalZ3 OAI.CriticalZ3.Box
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open Classical


theorem solution (B : Box) {y z z' : Vertex}
    (hy : ¬ B.Contains y) (hz : B.Contains z) (hz' : B.Contains z')
    (hyz : NearestNeighbor y z) (hyz' : NearestNeighbor y z') : z = z' := by
  obtain ⟨k, hk⟩ := not_forall.mp hy
  have hzk := hz k
  have hz'k := hz' k
  funext m
  have hzm := hz m
  have hz'm := hz' m
  obtain ⟨i, h | h⟩ := hyz <;> obtain ⟨j, h' | h'⟩ := hyz' <;>
  · have e1 := congrFun h k
    have e2 := congrFun h m
    have e3 := congrFun h' k
    have e4 := congrFun h' m
    simp only [step] at e1 e2 e3 e4
    split_ifs at e1 e2 e3 e4 <;> subst_vars <;> omega

