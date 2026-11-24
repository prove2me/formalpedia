-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.Tame.det_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:56:34.051613+00:00
-- url     : https://prove2.me/submissions/fad09b7e-851d-40f3-a1d0-230d6f903c78

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldTopologyNormBallsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDetStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockMatrixMulBlocks
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricCharacterModulusProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Tame_det_eq_coe

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.Tame
variable {F : Type} [Field F]
namespace GlobalTheory.CompanionTheory.QL.Tame
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (O : Subring F) (X : Matrix ι ι F)
    (hX : ∀ i j, X i j ∈ O) : X.det ∈ O := by
  rw [det_eq_coe O X hX]; exact Subtype.property _
end GlobalTheory.CompanionTheory.QL.Tame
