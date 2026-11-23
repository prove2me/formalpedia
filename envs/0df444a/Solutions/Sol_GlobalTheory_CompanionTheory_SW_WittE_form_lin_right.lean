-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.WittE.form_lin_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:32:10.697807+00:00
-- url     : https://prove2.me/submissions/63e71f6c-b1a4-41a7-939a-4ac6721ffbff

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
    B z (lin X c) = ∑ a, c a * B z (X a) := by
  simp [lin, map_sum]
end GlobalTheory.CompanionTheory.SW.WittE
