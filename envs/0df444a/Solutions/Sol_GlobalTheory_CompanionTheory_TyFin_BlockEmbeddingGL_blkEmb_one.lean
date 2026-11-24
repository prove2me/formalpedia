-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:49:17.385177+00:00
-- url     : https://prove2.me/submissions/d25467b2-657c-4128-9482-f9ea9b95a108

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlockEmbeddingGLInverse
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_BlockEmbeddingGL_blkEmb_row_ge
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_BlockEmbeddingGL_blkEmb_col_ge
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_BlockEmbeddingGL_blkEmb_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL
variable (K : Type) [Field K]
namespace GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL
theorem _root_.solution (d j : ℕ) : blkEmb K d j (1 : Matrix (Fin j) (Fin j) K) = 1 := by
  ext i l
  rw [Matrix.one_apply]
  by_cases hi : (i : ℕ) < j
  · by_cases hl : (l : ℕ) < j
    · rw [GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_lt K _ i l hi hl, Matrix.one_apply]
      simp [Fin.ext_iff]
    · exact GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_col_ge K _ i l (not_lt.1 hl)
  · exact GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_row_ge K _ i l (not_lt.1 hi)
end GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL
