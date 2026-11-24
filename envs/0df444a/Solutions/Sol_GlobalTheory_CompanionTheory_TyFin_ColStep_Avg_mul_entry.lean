-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.ColStep.Avg.mul_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:47:38.340064+00:00
-- url     : https://prove2.me/submissions/4685989b-65a7-4bc5-86b2-f408771500e6

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WhittakerVanishesOfRadicalSums
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_ColStep_Avg_unip_entry

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
theorem _root_.solution {u v : GL (Fin d) K} (hu : u ∈ patSet K (colGe d j))
    (hv : v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j)) {i l : Fin d}
    (hi : j ≤ (i : ℕ)) (hl : j ≤ (l : ℕ)) :
    ((u * v : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i l = (u : Matrix (Fin d) (Fin d) K) i l := by
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single l]
  · rw [unip_entry hv hl hl]
    simp
  · intro k _ hk
    by_cases hik : (u : Matrix (Fin d) (Fin d) K) i k = 0
    · simp [hik]
    · have hjk : j ≤ (k : ℕ) := by
        by_cases e : i = k
        · exact e ▸ hi
        · by_contra hn
          exact hik ((hu i k).2 e fun h => hn h.2)
      rw [unip_entry hv hjk hl, if_neg hk, mul_zero]
  · simp
end GlobalTheory.CompanionTheory.TyFin.ColStep.Avg
