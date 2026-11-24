-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FTransfer.actTup_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:20:16.517835+00:00
-- url     : https://prove2.me/submissions/af824b04-f057-4c09-8d9e-abe8ec1a035a

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitaryIsomOfIsometry
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FundamentalDomainTransportCongruentForm

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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FTransfer
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
namespace GlobalTheory.CompanionTheory.SW.FTransfer
theorem _root_.solution {M n : ℕ} (a b : GL (Fin M) (R ⊗[F] E)) (X : Fin n → Fin M → R ⊗[F] E) :
    actTup R (a * b) X = actTup R a (actTup R b X) := by
  funext c
  simp [actTup, Matrix.mulVec_mulVec]
end GlobalTheory.CompanionTheory.SW.FTransfer
