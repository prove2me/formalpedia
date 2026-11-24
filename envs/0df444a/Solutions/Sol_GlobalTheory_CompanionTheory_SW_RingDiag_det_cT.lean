-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.RingDiag.det_cT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:30:47.003697+00:00
-- url     : https://prove2.me/submissions/58f9bac5-3eba-481c-b7b3-c66a2a49cdb3

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinatePolynomialsFormMemKernelDifferential
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianUnitFormDiagonalizes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.RingDiag
open HeckeCharacterZeroLocus.SiegelWeilU
variable {A : Type} [CommRing A] {m : ℕ}
namespace GlobalTheory.CompanionTheory.SW.RingDiag
theorem _root_.solution (σ : A →+* A) (g : Matrix (Fin m) (Fin m) A) : (cT σ g).det = σ g.det := by
  rw [cT, Matrix.det_transpose, RingHom.map_det]; rfl
end GlobalTheory.CompanionTheory.SW.RingDiag
