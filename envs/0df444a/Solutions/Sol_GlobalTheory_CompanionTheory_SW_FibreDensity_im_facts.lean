-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FibreDensity.im_facts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:50.131666+00:00
-- url     : https://prove2.me/submissions/5390711d-40c0-4112-a7eb-ea6b4452165a

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
theorem _root_.solution {ψ : V → ℂ} (hc : Continuous ψ) (hs : HasCompactSupport ψ)
    {U : Set V} (hsupp : tsupport ψ ⊆ U) :
    Continuous (fun v => (ψ v).im) ∧ HasCompactSupport (fun v => (ψ v).im) ∧
      tsupport (fun v => (ψ v).im) ⊆ U := by
  have hsub : Function.support (fun v => (ψ v).im) ⊆ Function.support ψ := by
    intro v hv hv0
    exact hv (by simp [show ψ v = 0 from hv0])
  exact ⟨Complex.continuous_im.comp hc, hs.mono hsub, (closure_mono hsub).trans hsupp⟩
end GlobalTheory.CompanionTheory.SW.FibreDensity
