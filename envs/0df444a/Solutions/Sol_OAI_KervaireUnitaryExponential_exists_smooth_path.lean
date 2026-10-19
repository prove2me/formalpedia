-- Prove2me | solution 1 for OAI.KervaireUnitaryExponential.exists_smooth_path
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:47:19.977861+00:00
-- url     : https://prove2.me/submissions/98828127-4b52-41a8-bfc6-d32c4d8d2373

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
import Definitions.Def_OAI_GroupTheory_Kervaire_UnitaryHomotopy
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceDegree

open OAI OAI.KervaireUnitaryExponential
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
open scoped ContDiff
open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator
attribute [local instance] OAI.KervaireUnitaryExponential.instNormedAlgebraRat_oAI
variable {A : Type*} [CStarAlgebra A]
theorem kue_skew_log {A : Type*} [CStarAlgebra A] (u : unitary A) (hfin : (spectrum ℂ (u : A)).Finite) :
    ∃ a : A, star a = -a ∧ NormedSpace.exp a = (u : A) := by
  have hn : IsStarNormal (u : A) := isStarNormal_of_mem_unitary u.2
  have hcirc := spectrum.subset_circle_of_unitary (𝕜 := ℂ) u.2
  have hcont : ∀ g : ℂ → ℂ, ContinuousOn g (spectrum ℂ (u : A)) := by
    intro g
    have : DiscreteTopology (spectrum ℂ (u : A)) := by
      haveI := hfin.to_subtype; infer_instance
    rw [continuousOn_iff_continuous_restrict]
    exact continuous_of_discreteTopology
  refine ⟨cfc Complex.log (u : A), ?_, ?_⟩
  · rw [← cfc_star, ← cfc_neg]
    apply cfc_congr
    intro z hz
    have hz1 : ‖z‖ = 1 := by simpa using hcirc hz
    have hz0 : z ≠ 0 := by intro h; simp [h] at hz1
    simp only [Complex.star_def]
    apply Complex.ext
    · simp [Complex.log_re, hz1]
    · simp [Complex.log_im]
  · have hcfc : IsStarNormal (cfc Complex.log (u : A)) := cfc_predicate _ _
    rw [← CFC.complex_exp_eq_normedSpace_exp (a := cfc Complex.log (u : A)),
      ← cfc_comp Complex.exp Complex.log (u : A) (hf := hcont _)]
    conv_rhs => rw [← cfc_id ℂ (u : A)]
    apply cfc_congr
    intro z hz
    have hz1 : ‖z‖ = 1 := by simpa using hcirc hz
    have hz0 : z ≠ 0 := by intro h; simp [h] at hz1
    simp [Complex.exp_log hz0]

theorem solution (u : unitary A) (hfin : (spectrum ℂ (u : A)).Finite) :
    ∃ p : ℝ → A, ContDiff ℝ ∞ p ∧ p 0 = 1 ∧ p 1 = (u : A) ∧
      ∀ t, p t ∈ unitary A := by
  obtain ⟨a, ha, he⟩ := kue_skew_log u hfin
  have hska : a ∈ skewAdjoint A := by rw [skewAdjoint.mem_iff]; exact ha
  have hexp : ContDiff ℝ ∞ (fun x : A => NormedSpace.exp x) :=
    contDiff_iff_contDiffAt.mpr fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  refine ⟨fun t : ℝ => NormedSpace.exp (t • a), ?_, ?_, ?_, ?_⟩
  · exact hexp.comp (contDiff_id.smul contDiff_const)
  · simp
  · simpa using he
  · intro t
    exact NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem t hska)

