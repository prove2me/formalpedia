-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FourierPi.integral_subgroup_eq_real
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:55.864653+00:00
-- url     : https://prove2.me/submissions/ae40e6ff-3d21-4311-a0e6-1eb52bb1e03d

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
  {ψ : R → ℂ}
namespace GlobalTheory.CompanionTheory.SW.FourierPi
theorem _root_.solution (lam : Measure R) (A : Set R) (hA : MeasurableSet A) (t : R)
    (h : ∀ x ∈ A, ψ (x * t) = 1) : ∫ x in A, ψ (x * t) ∂lam = (lam.real A : ℂ) := by
  rw [setIntegral_congr_fun hA (g := fun _ => (1 : ℂ)) (fun x hx => h x hx)]
  simp [Measure.real]
end GlobalTheory.CompanionTheory.SW.FourierPi
