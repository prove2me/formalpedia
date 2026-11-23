-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FibreDensity.ae_eq_point
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:49.99426+00:00
-- url     : https://prove2.me/submissions/c41ae27d-a84a-48d4-b5dd-75c8aadd2234

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
theorem _root_.solution (hι : Function.Injective ι) (hf : ∀ v, f v = ι (g v))
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib) (b : X) :
    ∀ᵐ v ∂(fib b), g v = b := by
  have h1 : ∀ᵐ v ∂(fib b), v ∈ f ⁻¹' {ι b} ∩ g ⁻¹' B := by
    rw [ae_iff]; exact h.1 b
  filter_upwards [h1] with v hv
  exact hι ((hf v).symm.trans hv.1)
end GlobalTheory.CompanionTheory.SW.FibreDensity
