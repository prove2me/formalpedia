-- Prove2me | solution 1 for OAI.KervaireSpectral.cauchySeq_calculus
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:35:27.531832+00:00
-- url     : https://prove2.me/submissions/b919d89e-a990-40e8-9da5-5af84034e80a

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/SpectralMeasures.lean:L169-L206
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireSpectral.cauchySeq_calculus. The node keeps its source
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

/-- Bounded pointwise convergence of continuous spectral functions is strongly
Cauchy. The proof is scalar dominated convergence, applied to squared distances. -/
theorem cauchySeq_calculus (U : Operator H) [hU : IsStarNormal U]
    (f : ℕ → C(spectrum ℂ U, ℂ)) (g : spectrum ℂ U → ℂ)
    (C : ℝ) (_hC : 0 ≤ C) (hb : ∀ n z, ‖f n z‖ ≤ C)
    (ht : ∀ z, Tendsto (fun n => f n z) atTop (𝓝 (g z))) (ξ : H) :
    CauchySeq (fun n => cfcHom hU (f n) ξ) := by
  let F (p : ℕ × ℕ) (z : spectrum ℂ U) : ℝ :=
    Complex.normSq (f p.1 z - f p.2 z)
  have hF : ∀ p, AEStronglyMeasurable (F p) (vectorMeasure U ξ) := by
    intro p
    exact (Complex.continuous_normSq.comp ((f p.1).continuous.sub
      (f p.2).continuous)).aestronglyMeasurable
  have hbound : ∀ p z, ‖F p z‖ ≤ (2 * C) ^ 2 := by
    intro p z
    have hd : ‖f p.1 z - f p.2 z‖ ≤ 2 * C :=
      (norm_sub_le _ _).trans (by linarith [hb p.1 z, hb p.2 z])
    simp only [F, Complex.normSq_eq_norm_sq, Real.norm_eq_abs, abs_pow, abs_of_nonneg (norm_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) hd 2
  have hlim : ∀ z, Tendsto (fun p : ℕ × ℕ => F p z) atTop (𝓝 0) := by
    intro z
    rw [← prod_atTop_atTop_eq]
    simpa [F, Function.comp_def] using Complex.continuous_normSq.continuousAt.tendsto.comp
      (((ht z).comp tendsto_fst).sub ((ht z).comp tendsto_snd))
  have hi : Tendsto (fun p : ℕ × ℕ => ∫ z, F p z ∂vectorMeasure U ξ)
      atTop (𝓝 0) := by
    simpa using tendsto_integral_filter_of_dominated_convergence
      (fun _ => (2 * C) ^ 2) (Eventually.of_forall hF)
      (Eventually.of_forall fun p => Eventually.of_forall (hbound p))
      (integrable_const _) (Eventually.of_forall hlim)
  have heq : ∀ p : ℕ × ℕ, (∫ z, F p z ∂vectorMeasure U ξ) =
      ‖cfcHom hU (f p.1) ξ - cfcHom hU (f p.2) ξ‖ ^ 2 := by
    intro p
    simpa [normSqMap, map_sub, F] using integral_normSqMap U ξ (f p.1 - f p.2)
  simp_rw [heq] at hi
  apply cauchySeq_iff_tendsto_dist_atTop_0.mpr
  simpa only [Function.comp_def, dist_eq_norm, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
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


theorem solution : type_of% @_root_.OAI.KervaireSpectral.cauchySeq_calculus := @_root_.OAI.KervaireSpectral.cauchySeq_calculus
