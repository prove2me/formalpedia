-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.WittE.cT_mul_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:37:32.858844+00:00
-- url     : https://prove2.me/submissions/2a333f59-1fb1-4941-8a81-a134135b0c1a

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
theorem _root_.solution (s : E →+* E) {M : ℕ} (J g : Matrix (Fin M) (Fin M) E) (i j : Fin M) :
    (cT s g * J * g) i j = hform s J (fun k => g k i) (fun k => g k j) := by
  simp only [Matrix.mul_apply, cT, hform, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
end GlobalTheory.CompanionTheory.SW.WittE
