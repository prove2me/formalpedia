-- Prove2me | solution 1 for OAI.KervaireSpectral.sum_vectorPhase_grid
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:16:10.522362+00:00
-- url     : https://prove2.me/submissions/0634b885-97bb-4a93-9c1b-ff2f887a7cbd

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/PhaseGrids.lean:L98-L137
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireSpectral.sum_vectorPhase_grid. The node keeps its source
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
import Theorems.Thm_OAI_KervaireSpectral_sum_fract_grid
import Theorems.Thm_OAI_KervaireSpectral_vectorPhase_cfcHom
import Theorems.Thm_OAI_KervaireSpectral_vectorPhase_rotation

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

/-- Naturality for positive powers, needed for the boundary-cycle calculation. -/
theorem vectorPhase_pow (U : Operator H) (hU : U ∈ unitary (Operator H)) (n : ℕ) (ξ : H) :
    let _ := isStarNormal_of_mem_unitary hU
    let _ := isStarNormal_of_mem_unitary (pow_mem hU n)
    vectorPhase (U^n) ξ = ∫ z, phase ((z : ℂ)^n) ∂vectorMeasure U ξ := by
  let hN := isStarNormal_of_mem_unitary hU
  let f : C(spectrum ℂ U, ℂ) := ((ContinuousMap.id ℂ).restrict (spectrum ℂ U))^n
  have hf : cfcHom hN f = U^n := by
    dsimp [f]
    rw [map_pow, cfcHom_id]
  have hu : cfcHom hN f ∈ unitary (Operator H) := hf ▸ pow_mem hU n
  simpa only [hf, f, ContinuousMap.pow_apply, ContinuousMap.restrict_apply,
    ContinuousMap.id_apply] using vectorPhase_cfcHom U f hu ξ

end

theorem phase_rotation {z : ℂ} (hz : ‖z‖ = 1) (x : ℝ) :
    phase (scalarRotation x * z) = Int.fract (x + phase z) := by
  conv_lhs => rw [← exp_phase hz]
  change phase (scalarRotation x * scalarRotation (phase z)) = _
  rw [← scalarRotation_add]
  exact phase_exp_normalized _

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end KervaireSpectral

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.PhaseGrids ----
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

theorem phase_pow {z : ℂ} (hz : ‖z‖ = 1) (d : ℕ) :
    phase (z^d) = Int.fract ((d : ℝ)*phase z) := by
  conv_lhs => rw [← exp_phase hz]
  change phase (scalarRotation (phase z) ^ d) = _
  rw [← scalarRotation_nat_mul]
  exact phase_exp_normalized _

/-- The exact root-of-unity phase identity on the circle. -/
theorem sum_phase_grid {z : ℂ} (hz : ‖z‖ = 1) (d : ℕ) (hd : 0 < d) :
    (∑ j : Fin d, phase (scalarRotation ((j.val : ℝ)/d)*z)) =
      ((d : ℝ)-1)/2 + phase (z^d) := by
  simp_rw [phase_rotation hz, add_comm ((_:ℝ)/d) (phase z)]
  rw [sum_fract_grid d hd (phase z) ⟨phase_nonneg z, phase_lt_one z⟩, phase_pow hz]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Integrate the root-of-unity identity against a scalar spectral measure. -/
theorem sum_vectorPhase_grid (U : Operator H) (hU : U ∈ unitary (Operator H))
    (d : ℕ) (hd : 0 < d) (ξ : H) :
    let _ := isStarNormal_of_mem_unitary hU
    let _ := isStarNormal_of_mem_unitary (pow_mem hU d)
    let _ := fun j : Fin d => isStarNormal_of_mem_unitary
      (Unitary.smul_mem ⟨scalarRotation ((j.val : ℝ)/d), scalarRotation_unitary _⟩ hU)
    (∑ j : Fin d, vectorPhase (scalarRotation ((j.val : ℝ)/d) • U) ξ) =
      ((d : ℝ)-1)/2 * ‖ξ‖^2 + vectorPhase (U^d) ξ := by
  let _ := isStarNormal_of_mem_unitary hU
  let _ := isStarNormal_of_mem_unitary (pow_mem hU d)
  change (∑ j : Fin d, vectorPhase (scalarRotation ((j.val : ℝ)/d) • U) ξ) = _
  simp_rw [vectorPhase_rotation U hU]
  have hi (j : Fin d) : Integrable
      (fun z : spectrum ℂ U => phase (scalarRotation ((j.val : ℝ)/d) * z))
      (vectorMeasure U ξ) := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
      (measurable_phase.comp ((continuous_const.mul continuous_subtype_val).measurable)).aestronglyMeasurable
    filter_upwards [] with z
    change |phase _| ≤ 1
    rw [abs_of_nonneg (phase_nonneg _)]
    exact (phase_lt_one _).le
  rw [← integral_finsetSum _ (fun j _ => hi j)]
  have hp : Integrable (fun z : spectrum ℂ U => phase ((z : ℂ)^d)) (vectorMeasure U ξ) := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
      (measurable_phase.comp (continuous_subtype_val.pow d).measurable).aestronglyMeasurable
    filter_upwards [] with z
    change |phase _| ≤ 1
    rw [abs_of_nonneg (phase_nonneg _)]
    exact (phase_lt_one _).le
  have he (z : spectrum ℂ U) := sum_phase_grid (CStarRing.norm_of_mem_unitary
    (spectrum_subset_unitary_of_mem_unitary hU z.property)) d hd
  simp_rw [he]
  rw [integral_add (integrable_const _) hp, vectorPhase_pow U hU]
  congr 1
  have hm : (∫ _z : spectrum ℂ U, (1 : ℝ) ∂vectorMeasure U ξ) = ‖ξ‖^2 := by
    rw [integral_one_vectorMeasure, vectorCLM_apply]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) ξ
  rw [← hm, ← integral_const_mul]
  simp only [mul_one]

end

open KervaireTraceCalculus KervaireScalarPhase
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {ι κ : Type*} [Fintype ι] [Fintype κ]

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


theorem solution : type_of% @_root_.OAI.KervaireSpectral.sum_vectorPhase_grid := @_root_.OAI.KervaireSpectral.sum_vectorPhase_grid
