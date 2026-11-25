-- Prove2me | solution 1 for GlobalTheory.T.cuspidal_unipotent_radical_sum_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:03:21.492623+00:00
-- url     : https://prove2.me/submissions/78cb658e-98f4-446f-b47a-8c0df710b0f5

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalUnipotentRadicalSumZero
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalUnipotentRadicalSumZeroStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspSum_sum_character_translate


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
theorem _root_.solution : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (τ : FDRep ℂ (GL (Fin d) K)), 1 ≤ j → j < d → IsCuspidal K τ → ∀ u : GL (Fin d) K,
    (open Classical in ∑ v : GL (Fin d) K,
      if v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j) then τ.character (u * v) else 0) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.CuspSum.sum_character_translate | exact GlobalTheory.CompanionTheory.TyFin.CuspSum.sum_character_translate | (intros; apply GlobalTheory.CompanionTheory.TyFin.CuspSum.sum_character_translate <;> assumption)
end _root_.GlobalTheory.T
