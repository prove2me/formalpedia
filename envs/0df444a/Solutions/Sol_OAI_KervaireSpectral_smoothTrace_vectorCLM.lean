-- Prove2me | solution 1 for OAI.KervaireSpectral.smoothTrace_vectorCLM
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:02:32.533987+00:00
-- url     : https://prove2.me/submissions/7fbfaf41-3a38-4b74-8643-29d62bd78746

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/SpectralApproximation.lean:L106-L129
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireSpectral.smoothTrace_vectorCLM. The node keeps its source
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
import Theorems.Thm_OAI_KervaireSpectral_hasSum_spectralLog
import Theorems.Thm_OAI_KervaireSpectral_integral_vectorMeasure_complex

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

end KervaireSpectral

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.SpectralLogarithm ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology

namespace KervaireSpectral

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
open KervaireStrong

end

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every continuous function on the compact spectral space is integrable. -/
theorem integrable_continuous_map {E : Type*} [NormedAddCommGroup E]
    (U : Operator H) [IsStarNormal U] (ξ : H) (f : C(spectrum ℂ U, E)) :
    Integrable f (vectorMeasure U ξ) := by
  apply Integrable.mono' (integrable_const ‖f‖) f.continuous.aestronglyMeasurable
  exact Filter.Eventually.of_forall f.norm_coe_le_norm

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

/-- Applying any continuous functional to the convergent spectral logarithm
 commutes with its Mercator expansion. -/
theorem traceLog_eq_calculus (U : Operator H) (hU : U ∈ unitary (Operator H))
    (τ : Operator H →L[ℂ] ℂ) {a : ℂ} (ha : ‖a‖ < 1) :
    let hN := isStarNormal_of_mem_unitary hU
    traceLog τ a U = τ (cfcHom hN (spectralLog U hU a ha)) := by
  let hN := isStarNormal_of_mem_unitary hU
  have hc := (hasSum_spectralLog U hU ha).map (cfcHom hN) (cfcHom_continuous hN)
  have ht := hc.map τ τ.continuous
  apply HasSum.tsum_eq
  convert ht using 1
  ext n
  simp [map_smul, map_pow, cfcHom_id]

/-- The mass of a vector spectral measure is its value at the identity. -/
theorem integral_one_vectorMeasure (U : Operator H) [IsStarNormal U] (ξ : H) :
    ∫ _z : spectrum ℂ U, (1 : ℝ) ∂vectorMeasure U ξ = (vectorCLM ξ 1).re := by
  simpa using integral_vectorMeasure U ξ (1 : C(spectrum ℂ U, ℝ))

/-- Continuous-calculus and scalar-measure versions of the regularization agree. -/
theorem smoothTrace_vectorCLM (U : Operator H) (hU : U ∈ unitary (Operator H))
    (ξ : H) {a : ℂ} (ha : ‖a‖ < 1) :
    let _ := isStarNormal_of_mem_unitary hU
    smoothTrace (vectorCLM ξ) a U =
      ∫ z : spectrum ℂ U, smoothPhase a z ∂vectorMeasure U ξ := by
  let hN := isStarNormal_of_mem_unitary hU
  have hi := integrable_continuous_map U ξ (spectralLog U hU a ha)
  have he : (fun z : spectrum ℂ U => smoothPhase a z) =
      (fun z => 1 / 2 - (spectralLog U hU a ha z).im / Real.pi) := by
    funext z
    simp [spectralLog, smoothPhase, Complex.log_im, sub_eq_add_neg, neg_div]
  have him : Integrable (fun z => (spectralLog U hU a ha z).im) (vectorMeasure U ξ) :=
    Complex.imCLM.integrable_comp hi
  have hhalf : (∫ _z : spectrum ℂ U, (1 / 2 : ℝ) ∂vectorMeasure U ξ) =
      (vectorCLM ξ 1).re / 2 := by
    rw [integral_div, integral_one_vectorMeasure]
  change smoothTrace (vectorCLM ξ) a U = _
  rw [he, integral_sub (integrable_const _) (him.div_const _), hhalf, integral_div]
  have himint := Complex.imCLM.integral_comp_comm hi
  change (∫ z, (spectralLog U hU a ha z).im ∂vectorMeasure U ξ) = _ at himint
  rw [himint, integral_vectorMeasure_complex]
  exact congrArg (fun z : ℂ => (vectorCLM ξ 1).re / 2 - z.im / Real.pi)
    (traceLog_eq_calculus U hU (vectorCLM ξ) ha)

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
open KervaireTraceCalculus KervaireScalarPhase


theorem solution : type_of% @_root_.OAI.KervaireSpectral.smoothTrace_vectorCLM := @_root_.OAI.KervaireSpectral.smoothTrace_vectorCLM
