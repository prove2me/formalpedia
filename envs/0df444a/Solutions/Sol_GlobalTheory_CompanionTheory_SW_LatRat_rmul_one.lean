-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LatRat.rmul_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:27:45.817437+00:00
-- url     : https://prove2.me/submissions/ae18ce2b-cb4e-44f7-884d-c713b03e2bd5

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeStableAlmostEverywhere

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LatRat
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
omit [NumberField F]
namespace GlobalTheory.CompanionTheory.SW.LatRat
theorem _root_.solution (R : Type) [CommRing R] [Algebra F R] {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) :
    rmul R X 1 = X := by
  funext a i
  simp [rmul, Matrix.one_apply]
end GlobalTheory.CompanionTheory.SW.LatRat
