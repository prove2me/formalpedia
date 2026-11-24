-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BruhatInv.rank_cut_pm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:36:00.291826+00:00
-- url     : https://prove2.me/submissions/01084392-5338-433b-aaae-5208332c703e

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BruhatDecompositionUnique
import Theorems.Thm_GlobalTheory_CompanionTheory_BruhatInv_ind_mul_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_BruhatInv_mul_ind_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_BruhatInv_pm_apply

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
theorem _root_.solution (p q : ι → Prop) [DecidablePred p] [DecidablePred q] (σ : Equiv.Perm ι) :
    (ind K p * ((pm K σ : GL ι K) : Matrix ι ι K) * ind K q).rank =
      (Finset.univ.filter fun j => q j ∧ p (σ j)).card := by
  have h : ind K p * ((pm K σ : GL ι K) : Matrix ι ι K) * ind K q =
      ((pm K σ : GL ι K) : Matrix ι ι K) *
        Matrix.diagonal fun j => if q j ∧ p (σ j) then (1 : K) else 0 := by
    ext i j
    rw [mul_ind_apply, ind_mul_apply, Matrix.mul_diagonal, pm_apply]
    by_cases hij : i = σ j
    · subst hij
      by_cases h1 : p (σ j) <;> by_cases h2 : q j <;> simp [h1, h2]
    · simp [hij]
  rw [h, Matrix.rank_mul_eq_right_of_isUnit_det, Matrix.rank_diagonal, Fintype.card_subtype]
  · congr 1
    ext j
    by_cases h1 : q j ∧ p (σ j) <;> simp [h1]
  · exact (Matrix.isUnit_iff_isUnit_det _).1 (pm K σ).isUnit
end GlobalTheory.CompanionTheory.BruhatInv
