-- Prove2me | solution 2 for OAI.PlanarBoundary.balanced
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:18:18.107265+00:00
-- url     : https://prove2.me/submissions/d4bf9958-3a07-4dd1-afb5-017ad572b306

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/PlanarBoundary.lean:L49-L68
-- (upload_full_project.md Phase 4): solution for node OAI.PlanarBoundary.balanced. The node keeps its source
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
import Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths
import Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers
import Definitions.Def_OAI_Probability_CriticalZ3_SeedTrials
import Definitions.Def_OAI_Probability_CriticalZ3_Conditioning
import Definitions.Def_OAI_Probability_CriticalZ3_ConditionalQuality
import Definitions.Def_OAI_Probability_CriticalZ3_TrialCounts
import Definitions.Def_OAI_Probability_CriticalZ3_ShellProbability
import Definitions.Def_OAI_Probability_CriticalZ3_SeedQuality
import Definitions.Def_OAI_Probability_CriticalZ3_Scales
import Definitions.Def_OAI_Probability_CriticalZ3_Relay
import Definitions.Def_OAI_Probability_CriticalZ3_RelayProbability
import Definitions.Def_OAI_Probability_CriticalZ3_FiniteTrails
import Definitions.Def_OAI_Probability_CriticalZ3_PlanarBoundary

-- ---- from OAI.Probability.CriticalZ3.PlanarBoundary ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

/-! Oriented planar edge boundary with exact nearest-neighbor conventions. -/
open Classical
namespace PlanarBoundary
/-- At each dual vertex incoming and outgoing boundary degrees agree. -/
theorem balanced (X : Finset Point) (v : Point) :
    Fintype.card {e : Boundary X // head e = v} =
      Fintype.card {e : Boundary X // tail e = v} := by
  apply (Fintype.card_congr (atVertex X v headOffset)).trans
  apply Eq.trans _ (Fintype.card_congr (atVertex X v tailOffset)).symm
  simp only [Fintype.card_subtype,Finset.card_filter]
  simp only [Fin.sum_univ_succ,headOffset,tailOffset,outward,Matrix.cons_val_zero,
    Matrix.cons_val_succ]
  have ha : v-(1,0)+(0,-1) = v-(1,1) := by ext <;> simp [sub_eq_add_neg,add_assoc]
  have hb : v-(1,1)+(1,0) = v-(0,1) := by ext <;> simp
  have hc : v-(0,1)+(0,1) = v := sub_add_cancel _ _
  have hd : v+(-1,0) = v-(1,0) := by ext <;> simp [sub_eq_add_neg]
  have he : v+(0,-1) = v-(0,1) := by ext <;> simp [sub_eq_add_neg]
  have hf : v-(1,0)+(1,0) = v := sub_add_cancel _ _
  have hg : v-(1,1)+(0,1) = v-(1,0) := by ext <;> simp
  have hh : v-(0,1)+(-1,0) = v-(1,1) := by ext <;> simp [sub_eq_add_neg,add_assoc]
  simp only [show ((0,0) : Point) = 0 from rfl,sub_zero,ha,hb,hc,hd,he,hf,hg,hh]
  by_cases h0 : v ∈ X <;> by_cases h1 : v-(1,0) ∈ X <;>
    by_cases h2 : v-(1,1) ∈ X <;> by_cases h3 : v-(0,1) ∈ X <;> simp [h0,h1,h2,h3]

end PlanarBoundary

namespace PlanarBoundary
open Classical

end PlanarBoundary

namespace PlanarBoundary
open Classical

end PlanarBoundary

end OAI

-- ---- platform node ----
open OAI OAI.PlanarBoundary
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open Classical


theorem solution : type_of% @_root_.OAI.PlanarBoundary.balanced := @_root_.OAI.PlanarBoundary.balanced
