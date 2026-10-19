-- Prove2me | solution 2 for OAI.CriticalZ3.Coarse.cube_unique
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:36:30.253084+00:00
-- url     : https://prove2.me/submissions/ff4e3240-cc3e-4424-a049-d1d1b1e29554

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/Coarse.lean:L23-L39
-- (upload_full_project.md Phase 4): solution for node OAI.CriticalZ3.Coarse.cube_unique. The node keeps its source
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
import Definitions.Def_OAI_Probability_CriticalZ3_Matching
import Definitions.Def_OAI_Probability_CriticalZ3_Peierls
import Definitions.Def_OAI_Probability_CriticalZ3_Coarse

-- ---- from OAI.Probability.CriticalZ3.Coarse ----
namespace OAI

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
namespace Coarse
theorem cube_unique (r : ℕ) {v w : Point} {x : Vertex}
    (hv : (Q r v).Contains x) (hw : (Q r w).Contains x) : v = w := by
  have hg (a b t : ℤ) (h0 : (20*(r:ℤ)+1)*a-(10*r:ℕ) ≤ t)
      (h1 : t ≤ (20*(r:ℤ)+1)*a+(10*r:ℕ))
      (h2 : (20*(r:ℤ)+1)*b-(10*r:ℕ) ≤ t)
      (h3 : t ≤ (20*(r:ℤ)+1)*b+(10*r:ℕ)) : a = b := by
    push_cast at h0 h1 h2 h3
    have hr : (0:ℤ) ≤ r := Int.natCast_nonneg _
    by_contra h
    rcases lt_or_gt_of_ne h with hh|hh
    · have : a+1 ≤ b := by omega
      nlinarith
    · have : b+1 ≤ a := by omega
      nlinarith
  apply Prod.ext
  · exact hg v.1 w.1 (x 0) (hv 0).1 (hv 0).2 (hw 0).1 (hw 0).2
  · exact hg v.2 w.2 (x 1) (hv 1).1 (hv 1).2 (hw 1).1 (hw 1).2

end Coarse
end CriticalZ3

namespace CriticalZ3
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
namespace LatticeGraph

end LatticeGraph

namespace Coarse
end Coarse
end CriticalZ3

end OAI

-- ---- platform node ----
open OAI OAI.CriticalZ3 OAI.CriticalZ3.Coarse
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open _root_.MeasureTheory ProbabilityTheory Classical


theorem solution : type_of% @_root_.OAI.CriticalZ3.Coarse.cube_unique := @_root_.OAI.CriticalZ3.Coarse.cube_unique
