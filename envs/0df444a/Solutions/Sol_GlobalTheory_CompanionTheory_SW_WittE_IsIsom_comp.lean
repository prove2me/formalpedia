-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.WittE.IsIsom.comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:32:10.518993+00:00
-- url     : https://prove2.me/submissions/20c3bb74-736a-4360-b69a-01d3e8afec82

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_WittExtensionGlobal

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.WittE
variable {E V : Type} [Field E] [AddCommGroup V] [Module E V] {σ : E →+* E}
namespace GlobalTheory.CompanionTheory.SW.WittE
namespace IsIsom
theorem _root_.solution {B : V →ₛₗ[σ] V →ₗ[E] E} {γ δ : V →ₗ[E] V} (hγ : IsIsom B γ)
    (hδ : IsIsom B δ) : IsIsom B (γ ∘ₗ δ) := fun z w => by
  simp only [LinearMap.comp_apply, hγ _ _, hδ _ _]
end IsIsom
end GlobalTheory.CompanionTheory.SW.WittE
