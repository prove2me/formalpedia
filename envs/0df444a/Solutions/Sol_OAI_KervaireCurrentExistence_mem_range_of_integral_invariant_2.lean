-- Prove2me | solution 2 for OAI.KervaireCurrentExistence.mem_range_of_integral_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:31:06.51298+00:00
-- url     : https://prove2.me/submissions/2077e192-17c8-45d1-bdc8-a42824a93252

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/CurrentExistence.lean:L42-L82
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireCurrentExistence.mem_range_of_integral_invariant. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

-- ---- from OAI.GroupTheory.Kervaire.CurrentExistence ----
namespace OAI

noncomputable section

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

namespace KervaireCurrentExistence

variable {S E : Type*} [TopologicalSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {μ : Measure S} [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]

/-- The nonzero local degree forces a target point into the other endpoint's image.
All localization is justified by compactness, smooth bumps and positivity of Haar measure. -/
lemma mem_range_of_integral_invariant {f₀ f₁ : S → E} {j₀ j₁ : S → ℝ}
    (hf₀ : Continuous f₀) (hf₁ : Continuous f₁) (hj₀ : Continuous j₀)
    (y : E) (hex : ∃ x, f₀ x = y) (hpos : ∀ x, f₀ x = y → 0 < j₀ x)
    (hinv : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, φ (f₀ x) * j₀ x ∂μ) = ∫ x, φ (f₁ x) * j₁ x ∂μ) :
    y ∈ Set.range f₁ := by
  by_contra hmiss
  let K : Set E := f₀ '' {x | j₀ x ≤ 0} ∪ Set.range f₁
  have hK : IsCompact K := by
    apply IsCompact.union
    · exact (isClosed_le hj₀ continuous_const).isCompact.image hf₀
    · exact isCompact_range hf₁
  have hyK : y ∉ K := by
    rintro (⟨x, hx, hxy⟩ | hy)
    · exact (not_le_of_gt (hpos x hxy)) hx
    · exact hmiss hy
  obtain ⟨φ, hφs, hφcomp, hφ, hφrange, hφy⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (hK.isClosed.isOpen_compl.mem_nhds hyK)
  have hφzero (z : E) (hz : z ∈ K) : φ z = 0 := by
    by_contra hn
    exact hφs (subset_closure hn) hz
  have hnonneg (x : S) : 0 ≤ φ (f₀ x) * j₀ x := by
    by_cases hx : j₀ x ≤ 0
    · rw [hφzero _ (Or.inl ⟨x,hx,rfl⟩), zero_mul]
    · exact mul_nonneg (hφrange (mem_range_self _) |>.1) (le_of_not_ge hx)
  obtain ⟨x₀, hx₀⟩ := hex
  have hnonzero : φ (f₀ x₀) * j₀ x₀ ≠ 0 := by
    rw [hx₀, hφy, one_mul]
    exact (hpos x₀ hx₀).ne'
  have hgt : 0 < ∫ x, φ (f₀ x) * j₀ x ∂μ :=
    ((hφ.continuous.comp hf₀).mul hj₀).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (HasCompactSupport.of_compactSpace _) hnonneg hnonzero
  have hz : (∫ x, φ (f₁ x) * j₁ x ∂μ) = 0 := by
    apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall fun x ↦ by
      change φ (f₁ x) * j₁ x = 0
      rw [hφzero _ (Or.inr (mem_range_self x)), zero_mul]
  rw [hinv φ hφ hφcomp, hz] at hgt
  exact lt_irrefl _ hgt

end KervaireCurrentExistence

namespace KervaireIncidenceCurrent
open MeasureTheory KervaireUnitaryHomotopy
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]

end KervaireIncidenceCurrent

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireCurrentExistence
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


theorem solution : type_of% @_root_.OAI.KervaireCurrentExistence.mem_range_of_integral_invariant := @_root_.OAI.KervaireCurrentExistence.mem_range_of_integral_invariant
