-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BruhatInv.rank_cut_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:21:43.033281+00:00
-- url     : https://prove2.me/submissions/17d4dda8-a83f-4257-b5b7-61bcc466b2ad

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BruhatDecompositionUnique
import Theorems.Thm_GlobalTheory_CompanionTheory_BruhatInv_ind_mul_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_BruhatInv_mul_ind_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin Formalism.IrreducibleCountingLemmas.TYPES
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BruhatInv
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.BruhatInv
theorem _root_.solution (p q : ι → Prop) [DecidablePred p] [DecidablePred q] (A M B : Matrix ι ι K)
    (hA : ∀ i j, p i → ¬ p j → A i j = 0) (hB : ∀ i j, q j → ¬ q i → B i j = 0) :
    (ind K p * (A * M * B) * ind K q).rank ≤ (ind K p * M * ind K q).rank := by
  have h1 : ind K p * A = ind K p * A * ind K p := by
    ext i j
    rw [mul_ind_apply, ind_mul_apply]
    by_cases hi : p i <;> by_cases hj : p j <;> simp [hi, hj, hA i j]
  have h2 : B * ind K q = ind K q * (B * ind K q) := by
    ext i j
    rw [ind_mul_apply, mul_ind_apply]
    by_cases hi : q i <;> by_cases hj : q j <;> simp [hi, hj, hB i j]
  have h3 : ind K p * (A * M * B) * ind K q =
      (ind K p * A) * (ind K p * M * ind K q) * (B * ind K q) := by
    calc ind K p * (A * M * B) * ind K q = (ind K p * A) * M * (B * ind K q) := by
          simp only [Matrix.mul_assoc]
      _ = (ind K p * A * ind K p) * M * (ind K q * (B * ind K q)) := by rw [← h1, ← h2]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [h3]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
end GlobalTheory.CompanionTheory.BruhatInv
