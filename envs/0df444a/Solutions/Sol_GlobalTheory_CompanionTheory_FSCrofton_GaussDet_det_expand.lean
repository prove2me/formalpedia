-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FSCrofton.GaussDet.det_expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:33.993582+00:00
-- url     : https://prove2.me/submissions/1b506cf8-aa72-40e4-b490-16deea2fb4ea

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
theorem _root_.solution (G : Matrix β (Fin d) ℂ) (C : Fin d → β → ℂ) :
    ((Real.exp (-∑ k, ∑ j, ‖C k j‖ ^ 2) * ‖(Matrix.of C * G).det‖ ^ 2 : ℝ) : ℂ) =
      ∑ σ : Equiv.Perm (Fin d), ∑ τ : Equiv.Perm (Fin d),
        (((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ)) *
          ∏ k, rowF G (σ k) (τ k) (C k) := by
  set M := Matrix.of C * G with hMdef
  have hM : ∀ k a, M k a = ∑ i, C k i * G i a := fun k a => by
    simp [hMdef, Matrix.mul_apply]
  have hd : M.det = ∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, M k (σ k) := by
    rw [← Matrix.det_transpose, Matrix.det_apply']
    simp [Matrix.transpose_apply]
  have hc : conj M.det =
      ∑ τ : Equiv.Perm (Fin d), ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ k, conj (M k (τ k)) := by
    rw [hd, map_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_mul, map_prod]
    simp
  have hn : ((‖M.det‖ ^ 2 : ℝ) : ℂ) = M.det * conj M.det := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hE : ((Real.exp (-∑ k, ∑ j, ‖C k j‖ ^ 2) : ℝ) : ℂ) = ∏ k, eR (C k) := by
    simp only [eR]
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    push_cast
    rfl
  have hp : ∀ σ τ : Equiv.Perm (Fin d), ∏ k, rowF G (σ k) (τ k) (C k) =
      (∏ k, M k (σ k)) * (∏ k, conj (M k (τ k))) * ∏ k, eR (C k) := fun σ τ => by
    simp only [rowF, Finset.prod_mul_distrib, hM]
  rw [Complex.ofReal_mul, hn, hE]
  conv_lhs => rw [hc]; rw [hd]
  simp only [hp]
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  ring
end GlobalTheory.CompanionTheory.FSCrofton.GaussDet
