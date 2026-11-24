-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.ColStep.Avg.patChar_mul_unip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:06:51.110717+00:00
-- url     : https://prove2.me/submissions/deee2ddf-f38f-4720-8cbd-91cd4e38ebf8

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WhittakerVanishesOfRadicalSums
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_ColStep_Avg_mul_entry

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.ColStep GlobalTheory.CompanionTheory.TyFin.ColStep.Avg
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {d j : ℕ}
namespace GlobalTheory.CompanionTheory.TyFin.ColStep.Avg
theorem _root_.solution (ψ₀ : AddChar K ℂ) {u v : GL (Fin d) K} (hu : u ∈ patSet K (colGe d j))
    (hv : v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j)) :
    patChar (colGeE K d (j + 1)) ψ₀ (u * v) = patChar (colGeE K d (j + 1)) ψ₀ u := by
  unfold patChar
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  by_cases h : (l : ℕ) = i + 1 ∧ j + 1 ≤ (l : ℕ)
  · rw [mul_entry hu hv (by omega) (by omega)]
  · have hz : colGeE K d (j + 1) i l = 0 := if_neg h
    rw [hz, zero_mul, zero_mul]
end GlobalTheory.CompanionTheory.TyFin.ColStep.Avg
