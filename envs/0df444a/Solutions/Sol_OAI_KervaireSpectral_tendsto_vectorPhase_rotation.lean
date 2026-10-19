-- Prove2me | solution 1 for OAI.KervaireSpectral.tendsto_vectorPhase_rotation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:12:47.646462+00:00
-- url     : https://prove2.me/submissions/389b545b-03a5-408c-8e2f-d796a1cc0644

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/PhaseNaturality.lean:L163-L182
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireSpectral.tendsto_vectorPhase_rotation. The node keeps its source
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

end

theorem phase_rotation {z : ℂ} (hz : ‖z‖ = 1) (x : ℝ) :
    phase (scalarRotation x * z) = Int.fract (x + phase z) := by
  conv_lhs => rw [← exp_phase hz]
  change phase (scalarRotation x * scalarRotation (phase z)) = _
  rw [← scalarRotation_add]
  exact phase_exp_normalized _

/-- The exact one-sided convergence used at the exceptional boundary circle. -/
theorem tendsto_phase_rotation {ι : Type*} {l : Filter ι} {a : ι → ℝ}
    (ha : Tendsto a l (𝓝 0)) (ha0 : ∀ᶠ i in l, 0 ≤ a i)
    {z : ℂ} (hz : ‖z‖ = 1) :
    Tendsto (fun i => phase (scalarRotation (a i) * z)) l (𝓝 (phase z)) := by
  have ht : Tendsto (fun i => a i + phase z) l (𝓝 (phase z)) := by
    simpa only [zero_add] using ha.add_const (phase z)
  have he : (fun i => phase (scalarRotation (a i) * z)) =ᶠ[l]
      (fun i => a i + phase z) := by
    filter_upwards [ha0, ht.eventually (gt_mem_nhds (phase_lt_one z))] with i hi hi'
    rw [phase_rotation hz, Int.fract_eq_self.mpr ⟨add_nonneg hi (phase_nonneg z), hi'⟩]
  exact ht.congr' he.symm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Bounded convergence at the phase cut from the nonnegative-shift side. -/
theorem tendsto_vectorPhase_rotation (U : Operator H) (hU : U ∈ unitary (Operator H))
    (ξ : H) {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 0)) (ha0 : ∀ n, 0 ≤ a n) :
    let _ := isStarNormal_of_mem_unitary hU
    let _ := fun n => isStarNormal_of_mem_unitary (Unitary.smul_mem
      ⟨scalarRotation (a n), scalarRotation_unitary (a n)⟩ hU)
    Tendsto (fun n => vectorPhase (scalarRotation (a n) • U) ξ) atTop (𝓝 (vectorPhase U ξ)) := by
  let _ := isStarNormal_of_mem_unitary hU
  simp_rw [vectorPhase_rotation U hU]
  apply tendsto_integral_of_dominated_convergence (fun _ => 1)
  · intro n
    exact (measurable_phase.comp ((continuous_const.mul continuous_subtype_val).measurable)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (phase_nonneg _)]
    exact (phase_lt_one _).le
  · filter_upwards [] with z
    exact tendsto_phase_rotation ha (Eventually.of_forall ha0)
      (CStarRing.norm_of_mem_unitary (spectrum_subset_unitary_of_mem_unitary hU z.property))

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


theorem solution : type_of% @_root_.OAI.KervaireSpectral.tendsto_vectorPhase_rotation := @_root_.OAI.KervaireSpectral.tendsto_vectorPhase_rotation
