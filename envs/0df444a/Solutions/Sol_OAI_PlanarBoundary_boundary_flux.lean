-- Prove2me | solution 1 for OAI.PlanarBoundary.boundary_flux
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:21:34.948292+00:00
-- url     : https://prove2.me/submissions/2f62621d-61dd-45bf-a9ab-cf171ef42558

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
theorem pl_sideFlux_rev (x : Point) (d : Direction) :
    sideFlux (x + outward d) (opposite d) = - sideFlux x d := by
  obtain ⟨a, b⟩ := x
  fin_cases d <;> simp [sideFlux, rayFlux, tailOffset, headOffset, outward, opposite] <;> split_ifs <;> omega

theorem pl_cell_sum (x : Point) :
    ∑ d : Direction, sideFlux x d = if x = (0,0) then 1 else 0 := by
  obtain ⟨a, b⟩ := x
  rw [Fin.sum_univ_four]
  simp [sideFlux, rayFlux, tailOffset, headOffset, outward] <;> split_ifs <;> omega

theorem solution (X : Finset Point) :
    (∑ e : Boundary X, rayFlux (tail e) (head e)) = if (0,0) ∈ X then 1 else 0 := by
  let g : FullSide X → ℤ := fun e => sideFlux e.1.val e.2
  have h1 : (∑ e : Boundary X, rayFlux (tail e) (head e)) = ∑ e : {e : FullSide X // ¬isInternal e}, g e.val :=
    Fintype.sum_equiv (boundaryEquiv X) _ _ (fun e => rfl)
  have h2 : (∑ e : {e : FullSide X // isInternal e}, g e.val) = 0 := by
    have hc := Equiv.sum_comp (internalReverse X) (fun e => g e.val)
    have hp : ∀ e, g (internalReverse X e).val = - g e.val := by
      intro e
      show sideFlux (e.val.1.val + outward e.val.2) (opposite e.val.2) = _
      exact pl_sideFlux_rev _ _
    simp only [hp, Finset.sum_neg_distrib] at hc
    linarith
  have h3 := Fintype.sum_subtype_add_sum_subtype (fun e : FullSide X => isInternal e) g
  rw [h1, ← add_left_cancel_iff (a := ∑ e : {e : FullSide X // isInternal e}, g e.val), h3, h2, zero_add]
  rw [Fintype.sum_prod_type]
  simp only [g, pl_cell_sum]
  rw [Finset.sum_coe_sort X (fun x => if x = ((0:ℤ),(0:ℤ)) then (1:ℤ) else 0)]
  simp

