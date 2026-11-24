-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GramAlg.colM_rmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:19:04.42881+00:00
-- url     : https://prove2.me/submissions/8751384a-1a3f-4c83-8310-33b3ab85447e

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightActionIdentities

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GramAlg
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R]
variable {M n : ℕ}
namespace GlobalTheory.CompanionTheory.SW.GramAlg
theorem _root_.solution (X : Fin n → Fin M → R ⊗[F] E) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    colM (rmul R X g) = colM X * g := by
  ext i a
  simp [colM, rmul, Matrix.mul_apply]
end GlobalTheory.CompanionTheory.SW.GramAlg
