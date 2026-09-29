-- Prove2me | solution 1 for MeasureTheory.exists_integral_fourierChar_bilinForm_mul_ne_zero_of_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/7cd3ef8f-7251-5880-8c9f-53bc79ef5a33

import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Theorems.Thm_VectorFourier_ae_eq_zero_of_integrable_of_forall_fourierIntegral_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_exists_integral_fourierChar_bilinForm_mul_ne_zero_of_continuousOn

set_option autoImplicit false

open MeasureTheory

theorem solution
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure]
    (B : LinearMap.BilinForm ℝ V) (_hB : B.Nondegenerate)
    (G : V → ℂ) (_hG : Integrable G μ)
    (U : Set V) (_hU : IsOpen U) (_hGU : ContinuousOn G U)
    (z₀ : V) (_hz₀ : z₀ ∈ U) (_h0 : G z₀ ≠ 0) :
    ∃ u : V, ∫ z, ((Real.fourierChar (B z u) : Circle) : ℂ) * G z ∂μ ≠ 0 := by
  classical
  by_contra hex
  have hall : ∀ u : V, ∫ z, ((Real.fourierChar (B z u) : Circle) : ℂ) * G z ∂μ = 0 :=
    fun u => Classical.byContradiction fun h => hex ⟨u, h⟩

  have hF : ∀ w : V, VectorFourier.fourierIntegral Real.fourierChar μ B G w = 0 := by
    intro w
    have e1 : (fun v : V => Real.fourierChar (-(B v w)) • G v)
        = fun z => ((Real.fourierChar (B z (-w)) : Circle) : ℂ) * G z := by
      funext z
      rw [(B z).map_neg w, Circle.smul_def, smul_eq_mul]
    show (∫ v, Real.fourierChar (-(B v w)) • G v ∂μ) = 0
    rw [e1]
    exact hall (-w)
  have hae : G =ᵐ[μ] 0 :=
    VectorFourier.ae_eq_zero_of_integrable_of_forall_fourierIntegral_eq_zero μ B _hB G _hG hF

  obtain ⟨O, hO, hUO⟩ := (continuousOn_iff'.mp _hGU) {0}ᶜ isOpen_compl_singleton
  have hz : z₀ ∈ O ∩ U := by
    rw [← hUO]
    exact ⟨_h0, _hz₀⟩
  have hpos : 0 < μ (O ∩ U) := (hO.inter _hU).measure_pos μ ⟨z₀, hz⟩
  have hnull : μ {z | ¬ G z = (0 : V → ℂ) z} = 0 := ae_iff.mp hae
  have hsub : O ∩ U ⊆ {z | ¬ G z = (0 : V → ℂ) z} := by
    intro z hz'
    rw [← hUO] at hz'
    exact hz'.1
  exact hpos.ne' (measure_mono_null hsub hnull)

end S_MeasureTheory_exists_integral_fourierChar_bilinForm_mul_ne_zero_of_continuousOn
end P2MW
export P2MW.S_MeasureTheory_exists_integral_fourierChar_bilinForm_mul_ne_zero_of_continuousOn (solution)
