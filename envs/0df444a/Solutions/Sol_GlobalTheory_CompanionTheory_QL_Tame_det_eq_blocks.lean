-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.Tame.det_eq_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:56:33.10799+00:00
-- url     : https://prove2.me/submissions/4e40be86-7d9b-4417-9e39-eacfd435b2d2

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldTopologyNormBallsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDetStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockMatrixMulBlocks
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricCharacterModulusProperties
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.Tame
variable {F : Type} [Field F]
namespace GlobalTheory.CompanionTheory.QL.Tame
theorem _root_.solution {r c : ℕ} (M : Matrix (Fin (r + c)) (Fin (r + c)) F) :
    M.det = (Matrix.fromBlocks (bAA M) (bAD M) (bDA M) (bDD M)).det := by
  have h : M = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (bAA M) (bAD M) (bDA M) (bDD M)) := by
    ext i j
    induction i using Fin.addCases <;> induction j using Fin.addCases <;>
      simp [bAA, bAD, bDA, bDD]
  conv_lhs => rw [h]
  exact Matrix.det_reindex_self _ _
end GlobalTheory.CompanionTheory.QL.Tame
