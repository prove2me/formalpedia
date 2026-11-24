-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ModDet.det_transvections
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:32:17.934207+00:00
-- url     : https://prove2.me/submissions/23401903-de2d-4c73-af0f-806d029f6cb0

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MatrixTransvectionDiagonalDecompositionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarInvariantUnderTransvectionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MapMulVecEqSmul

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ModDet
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
  [LocallyCompactSpace K] [SecondCountableTopology K] [T2Space K] [MeasurableSpace K] [BorelSpace K]
namespace GlobalTheory.CompanionTheory.SW.ModDet
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι]
    (L : List (Matrix.TransvectionStruct ι K)) :
    ((L.map Matrix.TransvectionStruct.toMatrix).prod).det = 1 := by
  induction L with
  | nil => simp
  | cons t L ih => simp [Matrix.det_mul, ih, Matrix.TransvectionStruct.det]
end GlobalTheory.CompanionTheory.SW.ModDet
