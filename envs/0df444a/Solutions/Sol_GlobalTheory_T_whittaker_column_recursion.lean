-- Prove2me | solution 1 for GlobalTheory.T.whittaker_column_recursion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:26:01.731544+00:00
-- url     : https://prove2.me/submissions/6b544e21-3271-4841-aa35-494672bb629a

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WhittakerColumnRecursion
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WhittakerColumnRecursionStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_ColStep_Fourier_wh_colGe_succ_eq_sum


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
theorem _root_.solution : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (ψ₀ : AddChar K ℂ) (χ : GL (Fin d) K → ℂ), j < d →
    (patSet K (colGe d j)).ncard = Fintype.card K ^ j * (patSet K (colGe d (j + 1))).ncard →
    (∀ x : Fin j → K, (∑ r : Fin j → K, (ψ₀ (∑ i, r i * x i))⁻¹) = if x = 0 then (Fintype.card K : ℂ) ^ j else 0) →
    wh (colGe d (j + 1)) (colGeE K d (j + 1)) ψ₀ χ = ∑ r : Fin j → K, wh (colGe d j) (colGeR K d j r) ψ₀ χ := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.ColStep.Fourier.wh_colGe_succ_eq_sum | exact GlobalTheory.CompanionTheory.TyFin.ColStep.Fourier.wh_colGe_succ_eq_sum | (intros; apply GlobalTheory.CompanionTheory.TyFin.ColStep.Fourier.wh_colGe_succ_eq_sum <;> assumption)
end _root_.GlobalTheory.T
