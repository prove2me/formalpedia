-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FibreDensity.integral_fib_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:15:11.024562+00:00
-- url     : https://prove2.me/submissions/23d7d2fc-24c9-4beb-93fe-2edc1d0b3386

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityContinuousStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityUnique

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FibreDensity
variable {V X Y : Type}
  [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
  {μ : Measure V} {ν : Measure X} {f : V → Y} {g : V → X} {ι : X → Y} {B : Set X}
  {fib : X → Measure V}
namespace GlobalTheory.CompanionTheory.SW.FibreDensity
theorem _root_.solution (hfin : ∀ b, IsLocallyFiniteMeasure (fib b)) {ψ : V → ℂ}
    (hc : Continuous ψ) (hs : HasCompactSupport ψ) (b : X) :
    ∫ v, ψ v ∂(fib b) = ((∫ v, (ψ v).re ∂(fib b) : ℝ) : ℂ)
      + ((∫ v, (ψ v).im ∂(fib b) : ℝ) : ℂ) * Complex.I := by
  haveI := hfin b
  exact (integral_re_add_im (𝕜 := ℂ) (hc.integrable_of_hasCompactSupport hs)).symm
end GlobalTheory.CompanionTheory.SW.FibreDensity
