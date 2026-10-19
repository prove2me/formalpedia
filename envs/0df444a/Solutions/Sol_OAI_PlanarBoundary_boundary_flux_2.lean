-- Prove2me | solution 2 for OAI.PlanarBoundary.boundary_flux
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:20:06.883485+00:00
-- url     : https://prove2.me/submissions/430c42f8-772d-4af8-9cf3-1febcfaa68b9

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/PlanarBoundary.lean:L158-L179
-- (upload_full_project.md Phase 4): solution for node OAI.PlanarBoundary.boundary_flux. The node keeps its source
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
theorem reverse_tail (d : Direction) : outward d+tailOffset (opposite d) = headOffset d := by
  fin_cases d <;> decide

theorem reverse_head (d : Direction) : outward d+headOffset (opposite d) = tailOffset d := by
  fin_cases d <;> decide

theorem rayFlux_reverse (a b : Point) : rayFlux b a = -rayFlux a b := by
  unfold rayFlux
  ring

theorem sideFlux_reverse (cell : Point) (d : Direction) :
    sideFlux (cell+outward d) (opposite d) = -sideFlux cell d := by
  unfold sideFlux
  simp only [add_assoc,reverse_tail,reverse_head]
  exact rayFlux_reverse _ _

/-- The oriented boundary of one unit cell has ray intersection number one
exactly when it contains the ray's origin. No Jordan curve theorem is assumed. -/
theorem cell_flux (cell : Point) :
    (∑ d : Direction, sideFlux cell d) = if cell = (0,0) then 1 else 0 := by
  rcases cell with ⟨x,y⟩
  simp only [Fin.sum_univ_succ]
  simp [sideFlux,rayFlux,tailOffset,headOffset,Prod.ext_iff]
  split_ifs <;> omega

theorem internal_flux_zero (X : Finset Point) :
    (∑ e : {e : FullSide X // isInternal e}, sideFlux e.val.1.val e.val.2) = 0 := by
  let F : {e : FullSide X // isInternal e} → ℤ := fun e => sideFlux e.val.1.val e.val.2
  have hs := (internalReverse X).sum_comp F
  have he : (∑ e, F (internalReverse X e)) = -(∑ e, F e) := by
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro e _
    exact sideFlux_reverse _ _
  rw [he] at hs
  dsimp [F] at hs
  omega

/-- The whole finite boundary has nonzero positive-ray intersection number. -/
theorem boundary_flux (X : Finset Point) :
    (∑ e : Boundary X, rayFlux (tail e) (head e)) = if (0,0) ∈ X then 1 else 0 := by
  have hfull : (∑ e : FullSide X, sideFlux e.1.val e.2) = if (0,0) ∈ X then 1 else 0 := by
    rw [Fintype.sum_prod_type]
    simp_rw [cell_flux]
    rw [←Finset.sum_subtype X (by simp) (fun cell => if cell = (0,0) then (1 : ℤ) else 0)]
    simp
  have hpart : (∑ e : {e : FullSide X // isInternal e}, sideFlux e.val.1.val e.val.2) +
      (∑ e : {e : FullSide X // ¬isInternal e}, sideFlux e.val.1.val e.val.2) =
      ∑ e : FullSide X, sideFlux e.1.val e.2 := by
    have h₁ := Finset.sum_subtype (F := inferInstance) (Finset.univ.filter (isInternal (X := X)))
      (by simp : ∀ e : FullSide X, e ∈ Finset.univ.filter isInternal ↔ isInternal e)
      (fun e : FullSide X => sideFlux e.1.val e.2)
    have h₂ := Finset.sum_subtype (F := inferInstance) (Finset.univ.filter (fun e : FullSide X => ¬isInternal e))
      (by simp : ∀ e : FullSide X, e ∈ Finset.univ.filter (fun e => ¬isInternal e) ↔ ¬isInternal e)
      (fun e : FullSide X => sideFlux e.1.val e.2)
    rw [←h₁,←h₂]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  rw [internal_flux_zero,zero_add] at hpart
  rw [←hfull,←hpart]
  exact (boundaryEquiv X).sum_comp (fun e => sideFlux e.val.1.val e.val.2)

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


theorem solution : type_of% @_root_.OAI.PlanarBoundary.boundary_flux := @_root_.OAI.PlanarBoundary.boundary_flux
