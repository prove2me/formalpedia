-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.WittE.lin_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:32:09.756799+00:00
-- url     : https://prove2.me/submissions/bd078227-6217-464e-91db-455e2b1e7706

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
theorem _root_.solution {n : ℕ} (X : Fin n → V) (a : Fin n) : lin X (Pi.single a (1 : E)) = X a := by
  simp [lin, Pi.single_apply, ite_smul]
end GlobalTheory.CompanionTheory.SW.WittE
