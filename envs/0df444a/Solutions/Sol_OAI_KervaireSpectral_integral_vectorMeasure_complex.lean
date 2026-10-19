-- Prove2me | solution 1 for OAI.KervaireSpectral.integral_vectorMeasure_complex
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:42:21.281595+00:00
-- url     : https://prove2.me/submissions/5660e689-839e-4deb-80c0-87eff720a760

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/SpectralLogarithm.lean:L140-L161
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireSpectral.integral_vectorMeasure_complex. The node keeps its source
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

/-- The vector functional respects the star, without a trace assumption. -/
theorem vectorCLM_star (ξ : H) (T : Operator H) :
    vectorCLM ξ (star T) = star (vectorCLM ξ T) := by
  simp only [vectorCLM_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  exact (inner_conj_symm _ _).symm

/-- Real continuous spectral functions have real vector expectations. -/
theorem vectorCLM_complexify_real (U : Operator H) [hU : IsStarNormal U] (ξ : H)
    (f : C(spectrum ℂ U, ℝ)) :
    (((vectorCLM ξ (cfcHom hU (complexify f))).re : ℝ) : ℂ) =
      vectorCLM ξ (cfcHom hU (complexify f)) := by
  apply Complex.conj_eq_iff_re.mp
  change star (vectorCLM ξ (cfcHom hU (complexify f))) = _
  rw [← vectorCLM_star, ← map_star]
  congr 2
  ext z
  simp [complexify]

/-- Every continuous function on the compact spectral space is integrable. -/
theorem integrable_continuous_map {E : Type*} [NormedAddCommGroup E]
    (U : Operator H) [IsStarNormal U] (ξ : H) (f : C(spectrum ℂ U, E)) :
    Integrable f (vectorMeasure U ξ) := by
  apply Integrable.mono' (integrable_const ‖f‖) f.continuous.aestronglyMeasurable
  exact Filter.Eventually.of_forall f.norm_coe_le_norm

/-- The scalar spectral measure integrates complex functions as well as real ones. -/
theorem integral_vectorMeasure_complex (U : Operator H) [hU : IsStarNormal U] (ξ : H)
    (f : C(spectrum ℂ U, ℂ)) :
    ∫ z, f z ∂vectorMeasure U ξ = vectorCLM ξ (cfcHom hU f) := by
  let fr : C(spectrum ℂ U, ℝ) := ⟨fun z => (f z).re, Complex.continuous_re.comp f.continuous⟩
  let fi : C(spectrum ℂ U, ℝ) := ⟨fun z => (f z).im, Complex.continuous_im.comp f.continuous⟩
  have hf : f = complexify fr + Complex.I • complexify fi := by
    ext z
    change f z = ((f z).re : ℂ) + Complex.I * ((f z).im : ℂ)
    rw [mul_comm Complex.I]
    exact (Complex.re_add_im (f z)).symm
  have hr := integrable_continuous_map U ξ (complexify fr)
  have hi := integrable_continuous_map U ξ (complexify fi)
  change Integrable (fun z => (fr z : ℂ)) (vectorMeasure U ξ) at hr
  change Integrable (fun z => (fi z : ℂ)) (vectorMeasure U ξ) at hi
  rw [hf, map_add, map_smul, map_add, map_smul]
  change (∫ z, (fr z : ℂ) + Complex.I • (fi z : ℂ) ∂vectorMeasure U ξ) = _
  have hi' : Integrable (fun z => Complex.I • (fi z : ℂ)) (vectorMeasure U ξ) := by
    exact integrable_continuous_map U ξ (Complex.I • complexify fi)
  rw [integral_add hr hi', integral_smul]
  simp only [integral_complex_ofReal, integral_vectorMeasure,
    ← vectorCLM_apply, vectorCLM_complexify_real]

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


theorem solution : type_of% @_root_.OAI.KervaireSpectral.integral_vectorMeasure_complex := @_root_.OAI.KervaireSpectral.integral_vectorMeasure_complex
