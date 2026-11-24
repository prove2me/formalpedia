-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FSCrofton.GaussDet.perm_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:29:54.237551+00:00
-- url     : https://prove2.me/submissions/d2cc2bf9-5081-4e33-a75c-a1f84d739dd2

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetSquareIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FSCrofton GlobalTheory.CompanionTheory.FSCrofton.GaussDet
variable {β : Type} [Fintype β] [DecidableEq β]
variable {d : ℕ}
namespace GlobalTheory.CompanionTheory.FSCrofton.GaussDet
theorem _root_.solution (p : ℂ) (A : Matrix (Fin d) (Fin d) ℂ) :
    ∑ σ : Equiv.Perm (Fin d), ∑ τ : Equiv.Perm (Fin d),
        (((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ)) *
          ∏ k, (p * A (τ k) (σ k)) = p ^ d * (d.factorial : ℂ) * A.det := by
  have h1 : ∀ σ : Equiv.Perm (Fin d), ∑ τ : Equiv.Perm (Fin d),
      (((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ)) *
        ∏ k, (p * A (τ k) (σ k)) = p ^ d * A.det := fun σ => by
    have h2 := Matrix.det_permute' σ A
    rw [Matrix.det_apply'] at h2
    simp only [Matrix.submatrix_apply, id] at h2
    have hs : ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign σ : ℤ) : ℂ) = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    calc _ = ((Equiv.Perm.sign σ : ℤ) : ℂ) * p ^ d *
          ∑ τ : Equiv.Perm (Fin d), ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ k, A (τ k) (σ k) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun τ _ => ?_
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          ring
      _ = p ^ d * A.det := by
          rw [h2]
          linear_combination (p ^ d * A.det) * hs
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  ring
end GlobalTheory.CompanionTheory.FSCrofton.GaussDet
