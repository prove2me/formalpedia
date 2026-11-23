-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FourierPi.continuous_psi_dot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:55.4378+00:00
-- url     : https://prove2.me/submissions/f05bcffb-88b4-4e2c-9e96-dadf60e918e8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HarrisTaylorCardKilledByIdealEqAbsNormPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FourierPi
variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]
  {ψ : R → ℂ} {ι : Type} [Fintype ι]
namespace GlobalTheory.CompanionTheory.SW.FourierPi
theorem _root_.solution (hc : Continuous ψ) {X : Type} [TopologicalSpace X] {f g : X → ι → R}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun p => ψ (f p ⬝ᵥ g p) :=
  hc.comp (hf.dotProduct hg)
end GlobalTheory.CompanionTheory.SW.FourierPi
