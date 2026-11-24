-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FibreFam.BumpFamily.measurable_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:32:16.148931+00:00
-- url     : https://prove2.me/submissions/dbc256f9-c913-4e24-8e0f-7810c0a2aac1

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityContinuous
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreFam_exists_bump
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreFam_exists_exhaustion
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreFam_le_lintegral_bump
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreFam_lintegral_bump_le
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreFam_BumpFamily_measurable_lintegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FibreFam
variable {V X : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
variable [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
namespace GlobalTheory.CompanionTheory.SW.FibreFam
namespace BumpFamily
theorem _root_.solution [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V]
    {U : Set V} {B : Set X} {fib : X → Measure V}
    (h : BumpFamily U B fib) (hB : IsOpen B) {O : Set V} (hO : IsOpen O) (hOU : O ⊆ U) :
    Measurable fun b => fib b O := by
  obtain ⟨K, W, hKc, -, -, hKO, hKmono, -, hKU, -⟩ := exists_exhaustion hO
  have hφ : ∀ n, ∃ φ : V → ℝ, Continuous φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ O ∧ (∀ v, 0 ≤ φ v) ∧
      (∀ v, φ v ≤ 1) ∧ ∀ v ∈ K n, φ v = 1 := fun n => exists_bump (hKc n) hO (hKO n)
  choose φ hφc hφcs hφs hφ0 hφ1 hφK using hφ
  have hmeas : ∀ n, Measurable fun b => ∫⁻ v, ENNReal.ofReal (φ n v) ∂(fib b) := fun n =>
    h.measurable_lintegral hB (hφc n) (hφcs n) ((hφs n).trans hOU) (hφ0 n)
  refine measurable_of_tendsto_metrizable hmeas (tendsto_pi_nhds.mpr fun b => ?_)
  have hlow : Filter.Tendsto (fun n => fib b (K n)) Filter.atTop (𝓝 (fib b O)) := by
    have h2 := tendsto_measure_iUnion_atTop (μ := fib b) hKmono
    rw [hKU] at h2
    exact h2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    (fun n => le_lintegral_bump (fib b) (hKc n) (hφ0 n) (hφK n))
    (fun n => lintegral_bump_le (fib b) hO (hφ1 n) (hφs n))
end BumpFamily
end GlobalTheory.CompanionTheory.SW.FibreFam
