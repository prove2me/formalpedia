-- Prove2me | solution 1 for GlobalTheory.T.block_embedding_GL_inverse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:04:06.724895+00:00
-- url     : https://prove2.me/submissions/06ab7e2e-09b7-4a19-b741-49e478b44390

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlockEmbeddingGLInverse
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlockEmbeddingGLInverseStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_BlockEmbeddingGL_exists_gl_blkEmb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ), j ≤ d → ∀ g : GL (Fin j) K, ∃ h : GL (Fin d) K,
    (h : Matrix (Fin d) (Fin d) K) = blkEmb K d j (g : Matrix (Fin j) (Fin j) K) ∧
    ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = blkEmb K d j ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K) := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.exists_gl_blkEmb | exact GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.exists_gl_blkEmb | (intros; apply GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.exists_gl_blkEmb <;> assumption)
end _root_.GlobalTheory.T
