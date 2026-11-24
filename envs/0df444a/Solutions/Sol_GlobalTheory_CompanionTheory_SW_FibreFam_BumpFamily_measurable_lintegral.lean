-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FibreFam.BumpFamily.measurable_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:15:18.082724+00:00
-- url     : https://prove2.me/submissions/c9d3e916-0bf0-406c-ae31-773feb1636da

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityContinuous

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
theorem _root_.solution {U : Set V} {B : Set X} {fib : X → Measure V}
    (h : BumpFamily U B fib) (hB : IsOpen B) {φ : V → ℝ} (hc : Continuous φ)
    (hcs : HasCompactSupport φ) (hs : tsupport φ ⊆ U) (h0 : ∀ v, 0 ≤ φ v) :
    Measurable fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b) := by
  classical
  obtain ⟨h0B, hφ⟩ := h
  obtain ⟨hint, hcont⟩ := hφ φ hc hcs hs
  have heq : (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b)) =
      B.piecewise (fun b => ENNReal.ofReal (∫ v, φ v ∂(fib b))) (fun _ => 0) := by
    funext b
    by_cases hb : b ∈ B
    · simp only [Set.piecewise_eq_of_mem, hb]
      rw [ofReal_integral_eq_lintegral_ofReal (hint b hb) (ae_of_all _ h0)]
    · simp [Set.piecewise, hb, h0B b hb]
  rw [heq]
  exact (ENNReal.continuous_ofReal.comp_continuousOn hcont).measurable_piecewise continuousOn_const
    hB.measurableSet
end BumpFamily
end GlobalTheory.CompanionTheory.SW.FibreFam
