-- Prove2me | solution 1 for OAI.KervaireCurrentPullback.contDiff_of_multilinear
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:56:55.216412+00:00
-- url     : https://prove2.me/submissions/d9cbe1fd-0504-4a20-9429-d2be135f3b2a

import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase
import Definitions.Def_OAI_GroupTheory_Kervaire_TraceCalculus
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralApproximation
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseSubadditivity
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseNaturality
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseGrids
import Definitions.Def_OAI_GroupTheory_Kervaire_RegularOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixTrace
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixShifts
import Definitions.Def_OAI_GroupTheory_Kervaire_WeightedCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseFaithfulness
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseDimension
import Definitions.Def_OAI_GroupTheory_Kervaire_MixingOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_HaarCurrents
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentPullback

open OAI
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
theorem solution {n : ℕ} [FiniteDimensional ℝ F] [FiniteDimensional ℝ H]
    {f : E → F [⋀^Fin n]→L[ℝ] H}
    (hf : ContDiff ℝ ∞ (fun x ↦ (f x).toContinuousMultilinearMap)) :
    ContDiff ℝ ∞ f := by
  let L := ContinuousAlternatingMap.toContinuousMultilinearMapLI (𝕜 := ℝ) (E := F) (F := H) (ι := Fin n)
  obtain ⟨P, hP⟩ := LinearMap.exists_leftInverse_of_injective L.toLinearMap
    (LinearMap.ker_eq_bot.2 L.injective)
  haveI : FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ F) H) :=
    Module.Finite.of_injective ((ContinuousMultilinearMap.toMultilinearMapLinear (R' := ℝ) (A := ℝ) (M₁ := fun _ : Fin n ↦ F) (M₂ := H)))
      ContinuousMultilinearMap.toMultilinearMap_injective
  let P' := LinearMap.toContinuousLinearMap P
  have hfe : f = fun x ↦ P' ((f x).toContinuousMultilinearMap) := by
    funext x
    have := congrArg (fun T => T (f x)) hP
    simpa [P', L] using this.symm
  rw [hfe]
  exact P'.contDiff.comp hf

