-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.WittE.form_lin_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:37:36.70495+00:00
-- url     : https://prove2.me/submissions/20a75f8b-a885-49cf-8b25-a0cc90e30d9d

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
theorem _root_.solution (B : V →ₛₗ[σ] V →ₗ[E] E) {n : ℕ} (X : Fin n → V) (c : Fin n → E) (z : V) :
    B (lin X c) z = ∑ a, σ (c a) * B (X a) z := by
  simp [lin, map_sum, LinearMap.sum_apply]
end GlobalTheory.CompanionTheory.SW.WittE
