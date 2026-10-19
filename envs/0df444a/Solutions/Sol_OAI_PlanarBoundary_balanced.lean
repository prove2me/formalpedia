-- Prove2me | solution 1 for OAI.PlanarBoundary.balanced
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:17:06.221989+00:00
-- url     : https://prove2.me/submissions/57fa03fd-6435-4211-89ce-51e77c1d77e6

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

open OAI OAI.PlanarBoundary
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open Classical


theorem solution (X : Finset Point) (v : Point) :
    Fintype.card {e : Boundary X // head e = v} =
      Fintype.card {e : Boundary X // tail e = v} := by
  have h1 : Fintype.card {e : Boundary X // head e = v} = Fintype.card {d : Direction // v-headOffset d ∈ X ∧ v-headOffset d+outward d ∉ X} :=
    Fintype.card_congr (atVertex X v headOffset)
  have h2 : Fintype.card {e : Boundary X // tail e = v} = Fintype.card {d : Direction // v-tailOffset d ∈ X ∧ v-tailOffset d+outward d ∉ X} :=
    Fintype.card_congr (atVertex X v tailOffset)
  rw [h1, h2, Fintype.card_subtype, Fintype.card_subtype, Finset.card_filter, Finset.card_filter, Fin.sum_univ_four, Fin.sum_univ_four]
  obtain ⟨a, b⟩ := v
  simp [headOffset, tailOffset, outward]
  simp only [← sub_eq_add_neg] at *
  by_cases hA : (a-1, b-1) ∈ X <;> by_cases hB : (a-1, b) ∈ X <;> by_cases hC : (a, b) ∈ X <;> by_cases hD : (a, b-1) ∈ X <;> simp [hA, hB, hC, hD]

