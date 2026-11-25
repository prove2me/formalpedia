-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.PsiVolume.det_ne_of_mem_Jset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:38:11.174708+00:00
-- url     : https://prove2.me/submissions/e2055588-d53d-41c7-99bf-6049d0e6179b

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockMatrixMulBlocks
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParabolicElementBlocks
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldTopologyNormBallsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixAdditiveHaarNormalizedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MeasureInvertibleIntegralMatricesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_WeilIntegralUnipotentLeviFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.PsiVolume
variable {F : Type} [Field F]
namespace GlobalTheory.CompanionTheory.QL.PsiVolume
theorem _root_.solution {a : ℕ} {J' : Subgroup (GL (Fin a) F)} {Y : Matrix (Fin a) (Fin a) F}
    (h : Y ∈ Jset J') : Y.det ≠ 0 := by
  obtain ⟨k, -, rfl⟩ := h
  exact ((Matrix.isUnit_iff_isUnit_det _).1 k.isUnit).ne_zero
end GlobalTheory.CompanionTheory.QL.PsiVolume
