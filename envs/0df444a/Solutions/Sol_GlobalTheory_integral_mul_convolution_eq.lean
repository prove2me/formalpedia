-- Prove2me | solution 1 for GlobalTheory.integral_mul_convolution_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:01:21.964798+00:00
-- url     : https://prove2.me/submissions/623c412a-084a-45a8-a438-4b1756799925

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralMulConvolutionEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (H : Type) [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H]
    [MeasurableSpace H] [BorelSpace H] (μ : Measure H) (hμ : μ.IsHaarMeasure)
    (K : Set H) (hK : IsCompact K) (κ a : H → ℂ) (hκ : Continuous κ)
    (hκc : HasCompactSupport κ) (ha : Measurable a) (hai : Integrable a μ)
    (haK : ∀ x ∉ K, a x = 0) (f : H → ℂ) (hf : Continuous f) :
    ∫ z, f z * (∫ x, κ x * a (x⁻¹ * z) ∂μ) ∂μ = ∫ x, κ x * ∫ y, f (x * y) * a y ∂μ ∂μ := by
  haveI := hμ
  have hC : IsCompact (tsupport κ) := hκc
  obtain ⟨M, hM⟩ : ∃ M, ∀ w ∈ tsupport κ * K, ‖f w‖ ≤ M :=
    (hC.mul hK).exists_bound_of_continuousOn hf.continuousOn
  set G : H × H → ℂ := fun p => κ p.1 * (f p.2 * a (p.1⁻¹ * p.2)) with hG
  have hGm : AEStronglyMeasurable G (μ.prod μ) := by
    have h1 : Measurable fun p : H × H => a (p.1⁻¹ * p.2) :=
      ha.comp (measurable_fst.inv.mul measurable_snd)
    exact (hκ.comp continuous_fst).aestronglyMeasurable.mul
      ((hf.comp continuous_snd).aestronglyMeasurable.mul h1.aestronglyMeasurable)
  have hbound : Integrable (fun p : H × H => (‖κ p.1‖ * M) * ‖a p.2‖) (μ.prod μ) :=
    Integrable.mul_prod ((hκ.integrable_of_hasCompactSupport hκc).norm.mul_const M) hai.norm
  have hGs : Integrable (G ∘ fun p : H × H => (p.1, p.1 * p.2)) (μ.prod μ) := by
    refine hbound.mono' (hGm.comp_measurePreserving (measurePreserving_prod_mul μ μ)) ?_
    refine Filter.Eventually.of_forall fun p => ?_
    simp only [Function.comp, G, inv_mul_cancel_left]
    by_cases h1 : κ p.1 = 0
    · simp only [h1, zero_mul, norm_zero, mul_zero]; positivity
    by_cases h2 : a p.2 = 0
    · simp only [h2, mul_zero, norm_zero]; rfl
    have hx : p.1 ∈ tsupport κ := subset_tsupport _ h1
    have hy : p.2 ∈ K := by
      by_contra h; exact h2 (haK _ h)
    have hfM := hM _ (Set.mul_mem_mul hx hy)
    rw [norm_mul, norm_mul]
    calc ‖κ p.1‖ * (‖f (p.1 * p.2)‖ * ‖a p.2‖) ≤ ‖κ p.1‖ * (M * ‖a p.2‖) := by gcongr
      _ = ‖κ p.1‖ * M * ‖a p.2‖ := by ring
  have hGi : Integrable G (μ.prod μ) :=
    ((measurePreserving_prod_mul μ μ).integrable_comp hGm).1 hGs
  have hF : Integrable (Function.uncurry fun z x => f z * (κ x * a (x⁻¹ * z))) (μ.prod μ) := by
    refine hGi.swap.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.comp, G, Prod.fst_swap, Prod.snd_swap, Function.uncurry]
    ring
  calc ∫ z, f z * (∫ x, κ x * a (x⁻¹ * z) ∂μ) ∂μ
      = ∫ z, ∫ x, f z * (κ x * a (x⁻¹ * z)) ∂μ ∂μ := by
        congr 1; funext z; exact (integral_const_mul _ _).symm
    _ = ∫ x, ∫ z, f z * (κ x * a (x⁻¹ * z)) ∂μ ∂μ := integral_integral_swap hF
    _ = ∫ x, κ x * ∫ y, f (x * y) * a y ∂μ ∂μ := by
        congr 1; funext x
        rw [← integral_mul_left_eq_self (fun z => f z * (κ x * a (x⁻¹ * z))) x,
          ← integral_const_mul]
        congr 1; funext y
        simp only [inv_mul_cancel_left]
        ring
end GlobalTheory
