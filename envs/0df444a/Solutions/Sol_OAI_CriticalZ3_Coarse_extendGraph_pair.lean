-- Prove2me | solution 1 for OAI.CriticalZ3.Coarse.extendGraph_pair
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:11:15.463833+00:00
-- url     : https://prove2.me/submissions/3082af0a-9bf7-4b5e-a9d5-cd7f5d550bc7

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

open OAI OAI.CriticalZ3 OAI.CriticalZ3.Coarse
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open _root_.MeasureTheory ProbabilityTheory Classical


theorem solution (r : ℕ) (G : LatticeGraph) (v x : Point)
    (hv : G.ContainsBox (Q r v)) : (extendGraph r G v x hv).ContainsSet (PairRegion r v x) := by
  constructor
  · rintro y (hy | hy)
    · exact Finset.mem_union_left _ (hv.1 ((Box.mem_vertices _ _).mpr hy))
    · exact Finset.mem_union_right _ ((Box.mem_vertices _ _).mpr hy)
  · rintro e (h1 | h1) (h2 | h2)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hv.2 ((Box.mem_bonds _ _).mpr ⟨h1, h2⟩)))
    · exact Finset.mem_union_right _ ((mem_interface r v x e).mpr (Or.inl ⟨h1, h2⟩))
    · exact Finset.mem_union_right _ ((mem_interface r v x e).mpr (Or.inr ⟨h1, h2⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ ((Box.mem_bonds _ _).mpr ⟨h1, h2⟩))

