-- Prove2me | solution 1 for OAI.KervaireSpectral.tendsto_calculus
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:38:48.51264+00:00
-- url     : https://prove2.me/submissions/0995ff27-1150-4b94-9fc0-1d4393f0900a

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/SpectralMeasures.lean:L328-L357
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireSpectral.tendsto_calculus. The node keeps its source
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

/-- The scalar measure gives squared norms of arbitrary continuous-calculus vectors. -/
theorem integral_normSqMap (U : Operator H) [hU : IsStarNormal U] (ξ : H)
    (f : C(spectrum ℂ U, ℂ)) :
    ∫ z, normSqMap f z ∂vectorMeasure U ξ = ‖cfcHom hU f ξ‖ ^ 2 := by
  have hf : complexify (normSqMap f) = star f * f := by
    ext z
    exact Complex.normSq_eq_conj_mul_self
  rw [integral_vectorMeasure, hf, map_mul, map_star]
  change (inner ℂ ξ (star (cfcHom hU f) (cfcHom hU f ξ))).re = _
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

/-- An already continuous pointwise limit is identified by the scalar measures. -/
theorem tendsto_calculus (U : Operator H) [hU : IsStarNormal U]
    (f : ℕ → C(spectrum ℂ U, ℂ)) (g : C(spectrum ℂ U, ℂ))
    (C : ℝ) (_hC : 0 ≤ C) (hb : ∀ n z, ‖f n z‖ ≤ C)
    (ht : ∀ z, Tendsto (fun n => f n z) atTop (𝓝 (g z))) (ξ : H) :
    Tendsto (fun n => cfcHom hU (f n) ξ) atTop (𝓝 (cfcHom hU g ξ)) := by
  have hgb : ∀ z, ‖g z‖ ≤ C := fun z =>
    le_of_tendsto (ht z).norm (Eventually.of_forall fun n => hb n z)
  have hbound : ∀ n z, ‖normSqMap (f n - g) z‖ ≤ (2 * C) ^ 2 := by
    intro n z
    have hd : ‖f n z - g z‖ ≤ 2 * C :=
      (norm_sub_le _ _).trans (by linarith [hb n z, hgb z])
    simp only [normSqMap, ContinuousMap.coe_mk, ContinuousMap.sub_apply,
      Complex.normSq_eq_norm_sq, Real.norm_eq_abs, abs_pow, abs_of_nonneg (norm_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) hd 2
  have hlim : ∀ z, Tendsto (fun n => normSqMap (f n - g) z) atTop (𝓝 0) := by
    intro z
    simpa [normSqMap, Function.comp_def] using Complex.continuous_normSq.continuousAt.tendsto.comp
      ((ht z).sub (tendsto_const_nhds (x := g z)))
  have hi : Tendsto (fun n => ∫ z, normSqMap (f n - g) z ∂vectorMeasure U ξ)
      atTop (𝓝 0) := by
    simpa using tendsto_integral_of_dominated_convergence
      (fun _ => (2 * C) ^ 2)
      (fun n => (normSqMap (f n - g)).continuous.aestronglyMeasurable)
      (integrable_const _) (fun n => Eventually.of_forall (hbound n))
      (Eventually.of_forall hlim)
  simp_rw [integral_normSqMap, map_sub, sub_apply] at hi
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
    Real.continuous_sqrt.continuousAt.tendsto.comp hi

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


theorem solution : type_of% @_root_.OAI.KervaireSpectral.tendsto_calculus := @_root_.OAI.KervaireSpectral.tendsto_calculus
