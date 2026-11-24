-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.WittE.lin_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:37:38.258009+00:00
-- url     : https://prove2.me/submissions/5836a01a-f425-4c02-b792-6c5c7eb11e0b

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
theorem _root_.solution {n : ℕ} (X : Fin n → V) (c : Fin n → E) :
    lin X c ∈ Submodule.span E (Set.range X) :=
  Submodule.sum_mem _ fun a _ => Submodule.smul_mem (Submodule.span E (Set.range X)) _ (Submodule.subset_span ⟨a, rfl⟩)
end GlobalTheory.CompanionTheory.SW.WittE
