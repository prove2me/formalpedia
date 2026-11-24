-- Prove2me | solution 1 for GlobalTheory.T.GL_transitive_nonzero_vectors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:02:44.00422+00:00
-- url     : https://prove2.me/submissions/9a5a4942-264c-4d5e-9026-e9bd987272b1

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GLTransitiveNonzeroVectors
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GLTransitiveNonzeroVectorsStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_RowTrans_gl_transitive_rows


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
theorem _root_.solution : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (j : ℕ) (r r' : Fin j → K), r ≠ 0 → r' ≠ 0 →
    ∃ g : GL (Fin j) K, Matrix.vecMul r (g : Matrix (Fin j) (Fin j) K) = r' := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.RowTrans.gl_transitive_rows | exact GlobalTheory.CompanionTheory.TyFin.RowTrans.gl_transitive_rows | (intros; apply GlobalTheory.CompanionTheory.TyFin.RowTrans.gl_transitive_rows <;> assumption)
end _root_.GlobalTheory.T
