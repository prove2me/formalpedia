-- Prove2me | solution 1 for OAI.KervaireCurrentExistence.mem_range_of_integral_invariant
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:41:16.176667+00:00
-- url     : https://prove2.me/submissions/b64782dc-8cfe-46a6-8c41-ee8dc596f655

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
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentExistence

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
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder
open scoped ContDiff
open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator
open MeasureTheory Set Filter
open scoped Topology ContDiff
variable {S E : Type*} [TopologicalSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {μ : Measure S} [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]


theorem solution {f₀ f₁ : S → E} {j₀ j₁ : S → ℝ}
    (hf₀ : Continuous f₀) (hf₁ : Continuous f₁) (hj₀ : Continuous j₀)
    (y : E) (hex : ∃ x, f₀ x = y) (hpos : ∀ x, f₀ x = y → 0 < j₀ x)
    (hinv : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, φ (f₀ x) * j₀ x ∂μ) = ∫ x, φ (f₁ x) * j₁ x ∂μ) :
    y ∈ Set.range f₁ := by
  by_contra hy
  obtain ⟨x₀, hx₀⟩ := hex
  set F : Set S := {x | j₀ x ≤ 0} with hF
  have hFc : IsCompact F := isCompact_univ.of_isClosed_subset
    (isClosed_le hj₀ continuous_const) (Set.subset_univ _)
  set K : Set E := f₀ '' F ∪ Set.range f₁ with hK
  have hKc : IsCompact K := (hFc.image hf₀).union (isCompact_range hf₁)
  have hyK : y ∉ K := by
    rintro (⟨x, hx, hxy⟩ | hr)
    · have := hpos x hxy; simp only [hF, Set.mem_setOf_eq] at hx; linarith
    · exact hy hr
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hKc.isClosed.isOpen_compl y hyK
  let φ : ContDiffBump y := ⟨r / 2, r, by linarith, by linarith⟩
  have hφ0 : ∀ z, 0 ≤ φ z := fun z => φ.nonneg
  have hφK : ∀ z ∈ K, φ z = 0 := by
    intro z hz
    apply Function.notMem_support.mp
    rw [φ.support_eq]
    intro hz'
    exact hball hz' hz
  have h1 : (∫ x, φ (f₁ x) * j₁ x ∂μ) = 0 := by
    have : (fun x => φ (f₁ x) * j₁ x) = fun _ => 0 := by
      funext x; rw [hφK _ (Or.inr ⟨x, rfl⟩), zero_mul]
    rw [this, integral_zero]
  have hcont : Continuous (fun x => φ (f₀ x) * j₀ x) := (φ.continuous.comp hf₀).mul hj₀
  have hnn : 0 ≤ (fun x => φ (f₀ x) * j₀ x) := by
    intro x
    show 0 ≤ φ (f₀ x) * j₀ x
    by_cases hx : j₀ x ≤ 0
    · rw [hφK _ (Or.inl ⟨x, hx, rfl⟩), zero_mul]
    · exact mul_nonneg (hφ0 _) (le_of_lt (lt_of_not_ge hx))
  have hne : φ (f₀ x₀) * j₀ x₀ ≠ 0 := by
    rw [hx₀, φ.one_of_mem_closedBall (Metric.mem_closedBall_self φ.rIn_pos.le), one_mul]
    exact (hpos x₀ hx₀).ne'
  have h0 : 0 < ∫ x, φ (f₀ x) * j₀ x ∂μ :=
    hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _)) hnn hne
  have := hinv φ φ.contDiff φ.hasCompactSupport
  linarith

