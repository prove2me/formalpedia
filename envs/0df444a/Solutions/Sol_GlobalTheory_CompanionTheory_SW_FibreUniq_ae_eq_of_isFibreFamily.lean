-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FibreUniq.ae_eq_of_isFibreFamily
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:55.559703+00:00
-- url     : https://prove2.me/submissions/cb20d011-07f9-4a96-8db2-31260de8ed9f

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ContinuousDensitiesEqOfIntegralsOnCompactsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix Set
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FibreUniq
namespace GlobalTheory.CompanionTheory.SW.FibreUniq
theorem _root_.solution {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V]
    [TopologicalSpace X] [MeasurableSpace X] {μ : Measure V} {ν : Measure X} {f : V → Y}
    {g : V → X} {ι : X → Y} (hι : Function.Injective ι) (hf : ∀ v, f v = ι (g v))
    {U : Set V} {B : Set X} {fib : X → Measure V}
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν B fib) (b : X) :
    ∀ᵐ v ∂(fib b), g v = b ∧ v ∈ U := by
  have : ∀ᵐ v ∂(fib b), v ∈ f ⁻¹' {ι b} ∩ U := h.1 b
  filter_upwards [this] with v hv
  refine ⟨hι ?_, hv.2⟩
  rw [← hf v]
  exact hv.1
end GlobalTheory.CompanionTheory.SW.FibreUniq
