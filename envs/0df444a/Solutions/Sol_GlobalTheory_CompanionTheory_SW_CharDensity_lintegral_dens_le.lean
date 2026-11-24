-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.CharDensity.lintegral_dens_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:07:53.250874+00:00
-- url     : https://prove2.me/submissions/fd85d916-a4c6-4d50-94ec-458de4c01d60

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SchurFunctionCompactSupportModuloUnipotent
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_CharDensity_continuous_ker
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_CharDensity_bn_pos
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_CharDensity_tendsto_smoothed
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_CharDensity_lintegral_smoothed

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
theorem _root_.solution (μ : Measure V) [IsFiniteMeasure μ] (hφ : Integrable (phi μ) volume) :
    ∫⁻ y, ENNReal.ofReal (dens μ y).re ≤ μ Set.univ := by
  set a : ℕ → V → ℝ≥0∞ := fun n y => ENNReal.ofReal (∫ z, ker (bn n) (z - y) ∂μ) with ha
  have hlim : ∀ y, ENNReal.ofReal (dens μ y).re = liminf (fun n => a n y) atTop := by
    intro y
    have t := (Complex.continuous_re.tendsto _).comp (tendsto_smoothed μ hφ y)
    have t2 := (ENNReal.continuous_ofReal.tendsto _).comp t
    refine (Tendsto.liminf_eq ?_).symm
    simpa [Function.comp_def, ha] using t2
  have hmeas : ∀ n, Measurable (a n) := by
    intro n
    have hs : StronglyMeasurable (fun p : V × V => ker (bn n) (p.2 - p.1)) :=
      ((continuous_ker _).comp (by fun_prop)).stronglyMeasurable
    exact ENNReal.measurable_ofReal.comp (hs.integral_prod_right' (ν := μ)).measurable
  calc ∫⁻ y, ENNReal.ofReal (dens μ y).re = ∫⁻ y, liminf (fun n => a n y) atTop :=
        lintegral_congr hlim
    _ ≤ liminf (fun n => ∫⁻ y, a n y) atTop := lintegral_liminf_le hmeas
    _ = μ Set.univ := by
        simp only [ha, lintegral_smoothed μ (bn_pos _)]
        simp
end GlobalTheory.CompanionTheory.SW.CharDensity
