-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.StageValue.vec_one_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:33:35.478729+00:00
-- url     : https://prove2.me/submissions/ef42189d-0034-4c1c-8c60-3285f0f84f64

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductSupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.StageValue
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
namespace GlobalTheory.CompanionTheory.SW.StageValue
theorem _root_.solution {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) :
    vec ((1 : R) ⊗ₜ[F] (1 : E)) (0 : Fin n → R ⊗[F] E) X = consTup X := by
  rw [← Algebra.TensorProduct.one_def]
  rfl
end GlobalTheory.CompanionTheory.SW.StageValue
