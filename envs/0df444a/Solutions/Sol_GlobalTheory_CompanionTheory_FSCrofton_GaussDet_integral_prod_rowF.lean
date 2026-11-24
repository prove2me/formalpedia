-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FSCrofton.GaussDet.integral_prod_rowF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:36:13.913289+00:00
-- url     : https://prove2.me/submissions/bbea13f7-6a8a-4bb1-b43e-ae3cb0f85981

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetSquareIntegral
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussDet_integral_rowF

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
theorem _root_.solution (G : Matrix β (Fin d) ℂ) (σ τ : Equiv.Perm (Fin d)) :
    ∫ C : Fin d → β → ℂ, ∏ k, rowF G (σ k) (τ k) (C k) =
      ∏ k, ((Real.pi : ℂ) ^ Fintype.card β * (G.conjTranspose * G) (τ k) (σ k)) := by
  rw [integral_fintype_prod_volume_eq_prod (fun k : Fin d => rowF G (σ k) (τ k))]
  simp_rw [integral_rowF]
end GlobalTheory.CompanionTheory.FSCrofton.GaussDet
