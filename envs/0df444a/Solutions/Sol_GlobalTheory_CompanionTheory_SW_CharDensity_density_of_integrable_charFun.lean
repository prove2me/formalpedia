-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.CharDensity.density_of_integrable_charFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:44:55.356991+00:00
-- url     : https://prove2.me/submissions/4ae2e026-2693-4ead-b82b-c66624fcc3f7

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SchurFunctionCompactSupportModuloUnipotent
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_CharDensity_exists_density

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.CharDensity
open scoped FourierTransform
open Filter
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace GlobalTheory.CompanionTheory.SW.CharDensity
theorem _root_.solution :
    ∀ (κ : Type) [Fintype κ] (m : Measure (κ → ℝ)), IsFiniteMeasure m → Integrable (fun x : κ → ℝ => ∫ z, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * x w : ℝ) : ℂ)) ∂m) → ∃ D : (κ → ℝ) → ℝ, Continuous D ∧ (∀ y, 0 ≤ D y) ∧ (∀ y, (D y : ℂ) = ∫ x : κ → ℝ, (∫ z, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * x w : ℝ) : ℂ)) ∂m) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, y w * x w : ℝ) : ℂ))) ∧ ∀ U : Set (κ → ℝ), MeasurableSet U → m U = ∫⁻ y in U, ENNReal.ofReal (D y) := by
  intro κ _ m _ hint
  let e : (κ → ℝ) ≃ᵐ EuclideanSpace ℝ κ := MeasurableEquiv.toLp 2 _
  have hmp : MeasurePreserving e volume volume := PiLp.volume_preserving_toLp κ
  set μ : Measure (EuclideanSpace ℝ κ) := m.map e with hμ
  haveI : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  have hin : ∀ z x : κ → ℝ, inner ℝ (e z) (e x) = ∑ w, z w * x w := by
    intro z x
    simp only [e, MeasurableEquiv.toLp_apply, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    exact Finset.sum_congr rfl fun w _ => mul_comm _ _
  have hphi : ∀ x : κ → ℝ, phi μ (e x) =
      ∫ z, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * x w : ℝ) : ℂ)) ∂m := by
    intro x
    unfold phi
    rw [hμ, integral_map_equiv]
    simp_rw [hin]
  have hφ : Integrable (phi μ) volume := by
    rw [← hmp.integrable_comp_emb e.measurableEmbedding]
    exact hint.congr (Eventually.of_forall fun x => (hphi x).symm)
  obtain ⟨D, hc, h0, hD, hm⟩ := exists_density μ hφ
  refine ⟨D ∘ e, hc.comp (PiLp.continuous_toLp 2 _), fun y => h0 _, fun y => ?_, fun U hU => ?_⟩
  · rw [Function.comp_apply, hD]
    unfold dens
    rw [← hmp.integral_comp e.measurableEmbedding]
    simp_rw [hphi, hin]
  · have h1 : m U = μ (e.symm ⁻¹' U) := by
      rw [hμ, e.map_apply, ← Set.preimage_comp]
      simp
    rw [h1, hm, withDensity_apply _ (e.symm.measurable hU),
      ← hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding]
    simp [Function.comp_def, ← Set.preimage_comp]
end GlobalTheory.CompanionTheory.SW.CharDensity
