-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.WittE.formB_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:48.483803+00:00
-- url     : https://prove2.me/submissions/02c865af-82ca-42fd-8a11-741d38e0b9f8

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
variable {E : Type} [Field E]
namespace GlobalTheory.CompanionTheory.SW.WittE
theorem _root_.solution (s : E →+* E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → E) :
    formB s J x y = hform s J x y := rfl
end GlobalTheory.CompanionTheory.SW.WittE
