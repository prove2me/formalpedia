-- Prove2me | solution 1 for OAI.KervaireSpectral.vectorPhase_cfcHom
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:09:21.218475+00:00
-- url     : https://prove2.me/submissions/5c1f314e-9efc-4cdb-8a8d-695e2508702e

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/PhaseNaturality.lean:L21-L54
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireSpectral.vectorPhase_cfcHom. The node keeps its source
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

theorem phaseTriangle_nonneg (n : ℕ) {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) :
    0 ≤ phaseTriangle n x := by
  exact le_min hx (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hx'))

theorem phaseTriangle_le_self (n : ℕ) (x : ℝ) : phaseTriangle n x ≤ x := min_le_left _ _

theorem tendsto_phaseTriangle {x : ℝ} (hx : x < 1) :
    Tendsto (fun n => phaseTriangle n x) atTop (𝓝 x) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) * (1 - x)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_pos (by linarith) tendsto_const_nhds
  apply tendsto_const_nhds.congr'
  filter_upwards [ht.eventually (eventually_ge_atTop x)] with n hn
  exact (min_eq_left hn).symm

theorem phaseApprox_nonneg (U : Operator H) (hU : U ∈ unitary (Operator H))
    (n : ℕ) (z : spectrum ℂ U) : 0 ≤ phaseApprox U hU n z :=
  phaseTriangle_nonneg n (phase_nonneg _) (phase_lt_one _).le

theorem phaseApprox_le_one (U : Operator H) (hU : U ∈ unitary (Operator H))
    (n : ℕ) (z : spectrum ℂ U) : phaseApprox U hU n z ≤ 1 :=
  (phaseTriangle_le_self n _).trans (phase_lt_one _).le

theorem tendsto_phaseApprox (U : Operator H) (hU : U ∈ unitary (Operator H))
    (z : spectrum ℂ U) : Tendsto (fun n => phaseApprox U hU n z) atTop (𝓝 (phase z)) :=
  tendsto_phaseTriangle (phase_lt_one _)

theorem tendsto_integral_phaseApprox (U : Operator H) (hU : U ∈ unitary (Operator H))
    (ξ : H) : letI := isStarNormal_of_mem_unitary hU
    Tendsto (fun n => ∫ z, phaseApprox U hU n z ∂vectorMeasure U ξ)
      atTop (𝓝 (vectorPhase U ξ)) := by
  let := isStarNormal_of_mem_unitary hU
  apply tendsto_integral_of_dominated_convergence (fun _ => 1)
  · intro n
    exact (phaseApprox U hU n).continuous.aestronglyMeasurable
  · exact integrable_const _
  · intro n
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (phaseApprox_nonneg U hU n z)]
    exact phaseApprox_le_one U hU n z
  · exact Eventually.of_forall (tendsto_phaseApprox U hU)

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

/-- The cut-sensitive phase has the expected scalar-measure pullback under
continuous functional calculus. This is proved from triangular approximants. -/
theorem vectorPhase_cfcHom (U : Operator H) [hN : IsStarNormal U]
    (f : C(spectrum ℂ U, ℂ)) (hf : cfcHom hN f ∈ unitary (Operator H)) (ξ : H) :
    let _ := isStarNormal_of_mem_unitary hf
    vectorPhase (cfcHom hN f) ξ = ∫ z, phase (f z) ∂vectorMeasure U ξ := by
  let V := cfcHom hN f
  let _ := isStarNormal_of_mem_unitary hf
  let f' : C(spectrum ℂ U, spectrum ℂ V) :=
    ⟨fun z => ⟨f z, by
      rw [show spectrum ℂ V = Set.range f from cfcHom_map_spectrum hN f]
      exact Set.mem_range_self z⟩,
      continuous_induced_rng.mpr f.continuous⟩
  have he (n : ℕ) :
      (∫ z, phaseApprox V hf n z ∂vectorMeasure V ξ) =
        ∫ z, phaseApprox V hf n (f' z) ∂vectorMeasure U ξ := by
    change _ = ∫ z, ((phaseApprox V hf n).comp f') z ∂vectorMeasure U ξ
    rw [integral_vectorMeasure, integral_vectorMeasure]
    have hh := cfcHom_comp hN f f' (fun _ => rfl) (complexify (phaseApprox V hf n))
    exact congrArg (fun T : Operator H => (inner ℂ ξ (T ξ)).re) hh.symm
  have ht : Tendsto
      (fun n => ∫ z, phaseApprox V hf n (f' z) ∂vectorMeasure U ξ)
      atTop (𝓝 (∫ z, phase (f z) ∂vectorMeasure U ξ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => 1)
    · intro n
      exact ((phaseApprox V hf n).continuous.comp f'.continuous).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_of_nonneg (phaseApprox_nonneg V hf n (f' z))]
      exact phaseApprox_le_one V hf n (f' z)
    · exact Eventually.of_forall fun z => tendsto_phaseApprox V hf (f' z)
  exact tendsto_nhds_unique (tendsto_integral_phaseApprox V hf ξ)
    (by simpa only [he] using ht)

end

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

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


theorem solution : type_of% @_root_.OAI.KervaireSpectral.vectorPhase_cfcHom := @_root_.OAI.KervaireSpectral.vectorPhase_cfcHom
