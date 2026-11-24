-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.CharDensity.lintegral_smoothed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:50:29.93484+00:00
-- url     : https://prove2.me/submissions/8c60359b-d211-4290-8cc5-cee63814af01

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SchurFunctionCompactSupportModuloUnipotent
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_CharDensity_ker_nonneg
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_CharDensity_continuous_ker
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_CharDensity_integrable_ker
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_CharDensity_integral_ker
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_CharDensity_integrable_ker_shift

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
theorem _root_.solution (μ : Measure V) [IsFiniteMeasure μ] {b : ℝ} (hb : 0 < b) :
    ∫⁻ y, ENNReal.ofReal (∫ z, ker b (z - y) ∂μ) = μ Set.univ := by
  have h1 : ∀ y : V, ENNReal.ofReal (∫ z, ker b (z - y) ∂μ) =
      ∫⁻ z, ENNReal.ofReal (ker b (z - y)) ∂μ := fun y =>
    ofReal_integral_eq_lintegral_ofReal (integrable_ker_shift μ hb y)
      (Eventually.of_forall fun z => ker_nonneg hb _)
  simp_rw [h1]
  rw [lintegral_lintegral_swap]
  · have h2 : ∀ z : V, ∫⁻ y, ENNReal.ofReal (ker b (z - y)) = 1 := by
      intro z
      rw [← ofReal_integral_eq_lintegral_ofReal ((integrable_ker hb).comp_sub_left z)
        (Eventually.of_forall fun y => ker_nonneg hb _),
        integral_sub_left_eq_self (ker b) volume z, integral_ker hb, ENNReal.ofReal_one]
    simp_rw [h2]
    simp
  · have hc : Continuous (fun p : V × V => ker b (p.2 - p.1)) :=
      (continuous_ker b).comp (by fun_prop)
    exact (ENNReal.continuous_ofReal.comp hc).aemeasurable
end GlobalTheory.CompanionTheory.SW.CharDensity
