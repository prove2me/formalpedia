-- Prove2me | solution 1 for GlobalTheory.T.cuspidal_of_unipotent_sums_vanish
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:05:38.339581+00:00
-- url     : https://prove2.me/submissions/c6a28002-2e2e-48b9-ac4a-fd03203626ff

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalOfUnipotentSumsVanish
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalOfUnipotentSumsVanishStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspIff_isCuspidal_of_sum_char


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open Polynomial CategoryTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d : ℕ) (τ : FDRep ℂ (GL (Fin d) K)),
    (∀ a, 0 < a → a < d → (open Classical in ∑ u : GL (Fin d) K,
      if (∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨ ((i : ℕ) < a ∧ a ≤ (j : ℕ)))
      then τ.character u else 0) = 0) → IsCuspidal K τ := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.CuspIff.isCuspidal_of_sum_char | exact GlobalTheory.CompanionTheory.TyFin.CuspIff.isCuspidal_of_sum_char | (intros; apply GlobalTheory.CompanionTheory.TyFin.CuspIff.isCuspidal_of_sum_char <;> assumption)
end _root_.GlobalTheory.T
