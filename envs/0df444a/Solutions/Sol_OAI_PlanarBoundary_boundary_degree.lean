-- Prove2me | solution 1 for OAI.PlanarBoundary.boundary_degree
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:17:56.614534+00:00
-- url     : https://prove2.me/submissions/b8012db3-90e1-433a-8920-bbdc5de31994

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

open OAI OAI.PlanarBoundary
universe uAlpha uE uV
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open Classical


theorem solution (X : Finset Point) (v : Point) :
    Fintype.card {e : Boundary X // primalInside e = v ∨ primalOutside e = v} ≤ 4 := by
  have h := Fintype.card_le_of_injective
    (fun e : {e : Boundary X // primalInside e = v ∨ primalOutside e = v} => e.val.val.2) ?_
  · simpa using h
  rintro ⟨⟨⟨p, d⟩, hp1, hp2⟩, hp⟩ ⟨⟨⟨q, d'⟩, hq1, hq2⟩, hq⟩ h
  simp only at h
  subst h
  simp only [primalInside, primalOutside] at hp hq
  have : p = q := by
    rcases hp with hp | hp <;> rcases hq with hq | hq
    · rw [hp, hq]
    · subst hp; exact absurd (hq ▸ hp1) hq2
    · subst hq; exact absurd (hp ▸ hq1) hp2
    · exact add_right_cancel (hp.trans hq.symm)
  subst this
  rfl

