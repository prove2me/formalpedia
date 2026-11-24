-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Rescale.isFibreFamily_rescale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:30:53.914799+00:00
-- url     : https://prove2.me/submissions/c9091af1-6bea-4b8d-8b73-d04c176164dd

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FibreFamilySmul

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Rescale
namespace GlobalTheory.CompanionTheory.SW.Rescale
theorem _root_.solution (V X Y : Type) [TopologicalSpace V] [MeasurableSpace V]
    [TopologicalSpace X] [MeasurableSpace X] (μ : Measure V) (ν : Measure X) (f : V → Y)
    (ι : X → Y) (U : Set V) (B : Set X) (fib : X → Measure V)
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν B fib) (a c : ℝ≥0) (hc : c ≠ 0) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (a • μ) f ι U (c • ν) B (fun b => (a / c) • fib b) := by
  unfold Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily at h ⊢
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hφc hφs hφU => ?_⟩
  · rw [Measure.smul_apply, h.1 b, smul_zero]
  · simp only [Measure.restrict_smul, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
    rw [h.2.1 φ hφ, lintegral_const_mul' _ _ ENNReal.coe_ne_top, ← mul_assoc, ← ENNReal.coe_mul,
      mul_comm c, div_mul_cancel₀ a hc]
  · obtain ⟨h1, h2⟩ := h.2.2 φ hφc hφs hφU
    refine ⟨fun b hb => (h1 b hb).smul_measure_nnreal, ?_⟩
    have e : (fun b => ∫ v, φ v ∂((a / c) • fib b)) = fun b => ((a / c : ℝ≥0) : ℝ) • ∫ v, φ v ∂fib b := by
      funext b
      rw [integral_smul_nnreal_measure, NNReal.smul_def]
    rw [e]
    exact h2.const_smul ((a / c : ℝ≥0) : ℝ)
end GlobalTheory.CompanionTheory.SW.Rescale
