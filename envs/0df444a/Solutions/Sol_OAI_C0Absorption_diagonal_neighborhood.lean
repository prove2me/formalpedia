-- Prove2me | solution 1 for OAI.C0Absorption.diagonal_neighborhood
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:42:14.011673+00:00
-- url     : https://prove2.me/submissions/e2d799af-93b0-41aa-97b1-b211ca6a4dc5

import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization
import Definitions.Def_OAI_Analysis_C0Absorption_Coordinates
import Definitions.Def_OAI_Analysis_C0Absorption_Triangular
import Definitions.Def_OAI_Analysis_C0Absorption_Tests
import Definitions.Def_OAI_Analysis_C0Absorption_Duality
import Definitions.Def_OAI_Analysis_C0Absorption_Selection
import Definitions.Def_OAI_Analysis_C0Absorption_Supports
import Definitions.Def_OAI_Analysis_C0Absorption_Operations
import Definitions.Def_OAI_Analysis_C0Absorption_Detection
import Definitions.Def_OAI_Analysis_C0Absorption_Grid
import Definitions.Def_OAI_Analysis_C0Absorption_Weights
import Definitions.Def_OAI_Analysis_C0Absorption_Angles
import Definitions.Def_OAI_Analysis_C0Absorption_Blocks
import Definitions.Def_OAI_Analysis_C0Absorption_Correction
import Definitions.Def_OAI_Analysis_C0Absorption_Frozen
import Definitions.Def_OAI_Analysis_C0Absorption_Tags
import Definitions.Def_OAI_Analysis_C0Absorption_Operators
import Definitions.Def_OAI_Analysis_C0Absorption_Shift
import Definitions.Def_OAI_Analysis_C0Absorption_Space
import Definitions.Def_OAI_Analysis_C0Absorption_Finite
import Definitions.Def_OAI_Analysis_C0Absorption_FiniteShift

open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators


theorem solution {X Y G : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [NormedAddCommGroup G] (q : X → Y) {x : X} (hq : ContinuousAt q x)
    (A : Y × Y → G) (g : G) (hA : Tendsto A (nhds (q x,q x)) (nhds g))
    {ε : ℝ} (hε : 0<ε) :
    ∃ s : Set X, s∈nhds x ∧ ∀ y∈s, ∀ z∈s, ‖A (q y,q z)-g‖<ε := by
  have h1 : A ⁻¹' Metric.ball g ε ∈ nhds (q x, q x) := hA (Metric.ball_mem_nhds g hε)
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.1 h1
  refine ⟨q ⁻¹' (U ∩ V), hq (Filter.inter_mem hU hV), fun y hy z hz => ?_⟩
  have := hUV (Set.mk_mem_prod hy.1 hz.2)
  simpa [dist_eq_norm] using this

