-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.WittE.lin_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:48.418328+00:00
-- url     : https://prove2.me/submissions/7d453809-11aa-4e27-8600-c745e3bf2625

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
theorem _root_.solution {n : ℕ} (X : Fin n → V) (t : E) (c : Fin n → E) : lin X (t • c) = t • lin X c := by
  simp [lin, Finset.smul_sum, mul_smul]
end GlobalTheory.CompanionTheory.SW.WittE
