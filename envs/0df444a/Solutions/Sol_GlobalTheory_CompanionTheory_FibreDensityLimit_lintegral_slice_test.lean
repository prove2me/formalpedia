-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FibreDensityLimit.lintegral_slice_test
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:47:19.309679+00:00
-- url     : https://prove2.me/submissions/9f6b417f-bd94-4de6-90cd-727c2b1c4607

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DisintegrationInjectiveOpenMap
import Theorems.Thm_GlobalTheory_CompanionTheory_FibreDensityLimit_lintegral_slice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FibreDensityLimit
open Set
variable {V X Y : Type} [MeasurableSpace V] [TopologicalSpace V] [TopologicalSpace X] [MeasurableSpace X]
  {μ : Measure V} {ν : Measure X} {f : V → Y} {g : V → X} {ι : X → Y} {U : Set V} {fib : X → Measure V}
namespace GlobalTheory.CompanionTheory.FibreDensityLimit
theorem _root_.solution (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν univ fib)
    [BorelSpace V] (hUm : MeasurableSet U)
    (hι : Function.Injective ι) (hg : Measurable g) (hfg : ∀ v, f v = ι (g v)) {ψ : V → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U) (hψ0 : ∀ v, 0 ≤ ψ v)
    {A : Set X} (hA : MeasurableSet A) :
    ∫⁻ v in f ⁻¹' (ι '' A), ENNReal.ofReal (ψ v) ∂μ =
      ∫⁻ s in A, ENNReal.ofReal (∫ v, ψ v ∂(fib s)) ∂ν := by
  have hw0 : ∀ v, v ∉ U → ENNReal.ofReal (ψ v) = 0 := by
    intro v hv
    rw [image_eq_zero_of_notMem_tsupport (fun h' => hv (hψU h')), ENNReal.ofReal_zero]
  rw [lintegral_slice (w := fun v => ENNReal.ofReal (ψ v)) h hUm hι hg hfg
    (ENNReal.measurable_ofReal.comp hψ.measurable) hw0 hA]
  refine lintegral_congr fun s => ?_
  rw [ofReal_integral_eq_lintegral_ofReal ((h.2.2 ψ hψ hψc hψU).1 s (Set.mem_univ s))
    (Filter.Eventually.of_forall hψ0)]
end GlobalTheory.CompanionTheory.FibreDensityLimit
