-- Prove2me | solution 1 for OAI.KervaireIncidenceCurrent.contDiff_incidence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:58:04.993582+00:00
-- url     : https://prove2.me/submissions/b62f9806-f9a1-43e6-9314-229b4422cd3b

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
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceTangent

open OAI OAI.KervaireIncidenceCurrent
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
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]
theorem solution {f : ℝ × Mat K → Mat (K ⊕ R)} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (incidence f) := by
  unfold incidence
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × Alg K R => f (p.1, p.2.1)) :=
    hf.comp (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd))
  have h2 : ContDiff ℝ ∞ (fun p : ℝ × Alg K R => p.2.2.1) :=
    contDiff_fst.comp (contDiff_snd.comp contDiff_snd)
  have h4 : ContDiff ℝ ∞ (fun p : ℝ × Alg K R => p.2.2.2) :=
    contDiff_snd.comp (contDiff_snd.comp contDiff_snd)
  have h3 : ContDiff ℝ ∞ (fun p : ℝ × Alg K R => diag (1 : Mat K) (star p.2.2.2)) := by
    simp_rw [diag_eq_corner]
    exact contDiff_const.add ((in22 (K := K) (R := R)).contDiff.comp ((starL' ℝ : Mat R ≃L[ℝ] Mat R).contDiff.comp h4))
  exact ((h1.mul h2).mul h3).mul ((starL' ℝ : Mat (K ⊕ R) ≃L[ℝ] Mat (K ⊕ R)).contDiff.comp h2)

