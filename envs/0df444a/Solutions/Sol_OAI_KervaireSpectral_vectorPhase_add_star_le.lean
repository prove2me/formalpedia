-- Prove2me | solution 1 for OAI.KervaireSpectral.vectorPhase_add_star_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:39:46.157056+00:00
-- url     : https://prove2.me/submissions/be151d0c-bd8c-4cd6-9b06-c1d5acb0b842

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/PhaseFaithfulness.lean:L109-L133
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireSpectral.vectorPhase_add_star_le. The node keeps its source
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
import Theorems.Thm_OAI_KervaireSpectral_vectorPhase_cfcHom

-- ---- from OAI.GroupTheory.Kervaire.SpectralMeasures ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology

namespace KervaireSpectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-- The defining integration identity for the scalar spectral measure. -/
theorem integral_vectorMeasure (U : Operator H) [hU : IsStarNormal U] (ξ : H)
    (f : C(spectrum ℂ U, ℝ)) :
    ∫ z, f z ∂vectorMeasure U ξ = (inner ℂ ξ (cfcHom hU (complexify f) ξ)).re := by
  let fc : C_c(spectrum ℂ U, ℝ) := ⟨f, HasCompactSupport.of_compactSpace f⟩
  exact RealRMK.integral_rieszMeasure (vectorFunctional U ξ) fc

theorem phase_nonneg (z : ℂ) : 0 ≤ phase z := Int.fract_nonneg _

theorem phase_lt_one (z : ℂ) : phase z < 1 := Int.fract_lt_one _

theorem measurable_phase : Measurable phase :=
  (Complex.measurable_arg.div_const _).fract

/-- A bounded measurable phase is integrable for every scalar spectral measure. -/
theorem integrable_phase (U : Operator H) [IsStarNormal U] (ξ : H) :
    Integrable (fun z : spectrum ℂ U => phase z) (vectorMeasure U ξ) := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_phase.comp measurable_subtype_coe).aestronglyMeasurable
  filter_upwards [] with z
  simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (phase_nonneg _)] using (phase_lt_one z).le

theorem phase_exp_normalized (x : ℝ) :
    phase (Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)) = Int.fract x := by
  rw [phase_exp]
  congr 1
  field_simp

/-- Exponentiating the chosen phase recovers a point on the unit circle. -/
theorem exp_phase {z : ℂ} (hz : ‖z‖ = 1) :
    Complex.exp ((2 * Real.pi * phase z : ℝ) * Complex.I) = z := by
  have ha : 2 * Real.pi * phase z = z.arg - 2 * Real.pi *
      (Int.floor (z.arg / (2 * Real.pi)) : ℝ) := by
    unfold phase Int.fract
    field_simp
  change (Circle.exp (2 * Real.pi * phase z) : ℂ) = z
  rw [ha, Circle.exp_sub, Circle.exp_two_pi_mul_int, div_one]
  simpa only [hz, Complex.ofReal_one, one_mul, Circle.coe_exp] using
    Complex.norm_mul_exp_arg_mul_I z

end KervaireSpectral

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.SpectralApproximation ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology

namespace KervaireSpectral
open KervaireTraceCalculus KervaireScalarPhase
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The mass of a vector spectral measure is its value at the identity. -/
theorem integral_one_vectorMeasure (U : Operator H) [IsStarNormal U] (ξ : H) :
    ∫ _z : spectrum ℂ U, (1 : ℝ) ∂vectorMeasure U ξ = (vectorCLM ξ 1).re := by
  simpa using integral_vectorMeasure U ξ (1 : C(spectrum ℂ U, ℝ))

end KervaireSpectral

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.PhaseNaturality ----
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

namespace KervaireSpectral

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Naturality for taking the inverse of a unitary. -/
theorem vectorPhase_star (U : Operator H) (hU : U ∈ unitary (Operator H)) (ξ : H) :
    let _ := isStarNormal_of_mem_unitary hU
    let _ := isStarNormal_of_mem_unitary (Unitary.star_mem hU)
    vectorPhase (star U) ξ = ∫ z, phase (star (z : ℂ)) ∂vectorMeasure U ξ := by
  let hN := isStarNormal_of_mem_unitary hU
  let f : C(spectrum ℂ U, ℂ) := star ((ContinuousMap.id ℂ).restrict (spectrum ℂ U))
  have hf : cfcHom hN f = star U := by
    dsimp [f]
    rw [map_star, cfcHom_id]
  have hu : cfcHom hN f ∈ unitary (Operator H) := hf ▸ Unitary.star_mem hU
  simpa only [hf, f, ContinuousMap.star_apply, ContinuousMap.restrict_apply,
    ContinuousMap.id_apply] using vectorPhase_cfcHom U f hu ξ

end

theorem phase_star {z : ℂ} (hz : ‖z‖ = 1) : phase (star z) = Int.fract (-phase z) := by
  conv_lhs => rw [← exp_phase hz]
  change phase (star (scalarRotation (phase z))) = _
  rw [star_scalarRotation]
  exact phase_exp_normalized _

theorem phase_add_star_le_one {z : ℂ} (hz : ‖z‖ = 1) :
    phase z + phase (star z) ≤ 1 := by
  rw [phase_star hz]
  simpa only [Int.fract_eq_self.mpr ⟨phase_nonneg z, phase_lt_one z⟩, add_neg_cancel, Int.fract_zero, zero_add] using
    Int.fract_add_fract_le (phase z) (-phase z)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end KervaireSpectral

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.PhaseFaithfulness ----
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

namespace KervaireRegular
open KervaireSpectral
open scoped ComplexOrder
variable {A : Type*} [Group A]

end KervaireRegular

namespace KervaireSpectral
open KervaireTraceCalculus
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- An inverse pair contributes at most one unit of phase per unit vector. -/
theorem vectorPhase_add_star_le (U : Operator H) (hU : U ∈ unitary (Operator H)) (ξ : H) :
    let _ := isStarNormal_of_mem_unitary hU
    let _ := isStarNormal_of_mem_unitary (Unitary.star_mem hU)
    vectorPhase U ξ + vectorPhase (star U) ξ ≤ ‖ξ‖^2 := by
  let _ := isStarNormal_of_mem_unitary hU
  let _ := isStarNormal_of_mem_unitary (Unitary.star_mem hU)
  have hi : Integrable (fun z : spectrum ℂ U => phase (star (z : ℂ))) (vectorMeasure U ξ) := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
      (measurable_phase.comp (continuous_subtype_val.star.measurable)).aestronglyMeasurable
    filter_upwards [] with z
    change |phase (star (z : ℂ))| ≤ 1
    rw [abs_of_nonneg (phase_nonneg _)]
    exact (phase_lt_one _).le
  change vectorPhase U ξ + vectorPhase (star U) ξ ≤ ‖ξ‖^2
  rw [vectorPhase_star U hU, vectorPhase, ← integral_add (integrable_phase U ξ) hi]
  calc
    (∫ z, (phase (z : ℂ) + phase (star (z : ℂ))) ∂vectorMeasure U ξ) ≤ ∫ _z, (1 : ℝ) ∂vectorMeasure U ξ := by
      apply integral_mono ((integrable_phase U ξ).add hi) (integrable_const _)
      intro z
      exact phase_add_star_le_one (CStarRing.norm_of_mem_unitary
        (spectrum_subset_unitary_of_mem_unitary hU z.property))
    _ = ‖ξ‖^2 := by
      rw [integral_one_vectorMeasure, vectorCLM_apply]
      exact inner_self_eq_norm_sq (𝕜 := ℂ) ξ

end KervaireSpectral

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireSpectral
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open KervaireTraceCalculus


theorem solution : type_of% @_root_.OAI.KervaireSpectral.vectorPhase_add_star_le := @_root_.OAI.KervaireSpectral.vectorPhase_add_star_le
