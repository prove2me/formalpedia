-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FiberInt.lintegral_periodized
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:30:03.635126+00:00
-- url     : https://prove2.me/submissions/88fa4755-6b04-44fb-a097-3d81f577a649

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarMeasureSplitExactSequence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FiberInt
variable {A A' : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [LocallyCompactSpace A] [T2Space A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]
  [AddCommGroup A'] [TopologicalSpace A'] [IsTopologicalAddGroup A'] [LocallyCompactSpace A']
  [T2Space A'] [SecondCountableTopology A'] [MeasurableSpace A'] [BorelSpace A']
namespace GlobalTheory.CompanionTheory.FiberInt
theorem _root_.solution {π : A →+ A'} (hπ : Measurable π) {Γ' : AddSubgroup A'} [Countable Γ']
    (lam : Measure A) (𝓖 : Set A) {f : A' → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂(periodized π Γ' lam 𝓖) = ∫⁻ x in 𝓖, ∑' γ : Γ', f ((γ : A') + π x) ∂lam := by
  rw [show periodized π Γ' lam 𝓖 = Measure.sum (fun γ : Γ' => ((lam.restrict 𝓖).map π).map ((γ : A') + ·)) from rfl, lintegral_sum_measure,
    lintegral_tsum]
  · refine tsum_congr fun γ => ?_
    rw [lintegral_map hf (measurable_const_add _), lintegral_map _ hπ]
    exact hf.comp (measurable_const_add _)
  · intro γ
    exact (hf.comp ((measurable_const_add _).comp hπ)).aemeasurable
end GlobalTheory.CompanionTheory.FiberInt
