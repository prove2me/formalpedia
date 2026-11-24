-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.ColStep.Fourier.patChar_colGeR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:06:52.115805+00:00
-- url     : https://prove2.me/submissions/291fbb26-6d78-44c6-ac7b-c2f192121372

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WhittakerColumnRecursion
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_ColStep_Fourier_sum_dite_col

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.ColStep GlobalTheory.CompanionTheory.TyFin.ColStep.Fourier
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
namespace GlobalTheory.CompanionTheory.TyFin.ColStep.Fourier
theorem _root_.solution {d j : ℕ} (hj : j < d) (r : Fin j → K) (ψ₀ : AddChar K ℂ) (u : GL (Fin d) K) :
    patChar (colGeR K d j r) ψ₀ u =
      patChar (colGeE K d (j + 1)) ψ₀ u * ψ₀ (∑ i, r i * colEntries hj u i) := by
  unfold patChar
  rw [← AddChar.map_add_eq_mul]
  congr 1
  rw [show (∑ i, r i * colEntries hj u i) =
      ∑ i : Fin j, r i * (u : Matrix (Fin d) (Fin d) K) ⟨i, i.2.trans hj⟩ ⟨j, hj⟩ from rfl,
    ← sum_dite_col hj r (u : Matrix (Fin d) (Fin d) K), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  unfold colGeR
  ring
end GlobalTheory.CompanionTheory.TyFin.ColStep.Fourier
