-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Cont.integrable_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:38:28.993707+00:00
-- url     : https://prove2.me/submissions/bf4cace9-dc58-4140-a6a5-79eef6b7638d

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ArchimedeanOrbitalIntegralContinuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Cont
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Cont
theorem _root_.solution {E : Type} [AddCommGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [MeasurableSpace E] [BorelSpace E]
    (N : ℕ) (e : E ≃+ (Fin N → ℝ)) (he : Continuous e) (hes : Continuous e.symm)
    (f : SchwartzMap (Fin N → ℝ) ℂ) (μ : Measure E) [μ.IsAddHaarMeasure] :
    Integrable (fun X => f (e X)) μ := by
  haveI : (Measure.map e μ).IsAddHaarMeasure := e.isAddHaarMeasure_map μ he hes
  have hs := Measure.isAddLeftInvariant_eq_smul (Measure.map e μ)
    (volume : Measure (Fin N → ℝ))
  have hi : Integrable f (Measure.map e μ) := by
    rw [hs]
    exact (f.integrable (μ := volume)).smul_measure_nnreal
  exact hi.comp_measurable he.measurable
end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Cont
