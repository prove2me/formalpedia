-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FSCrofton.GaussDet.row_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:34.623682+00:00
-- url     : https://prove2.me/submissions/3145e8ca-9baa-4afc-9b13-7c676dc40ae5

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
namespace GlobalTheory.CompanionTheory.FSCrofton.GaussDet
theorem _root_.solution (i j : β) (r : β → ℂ) :
    r i * conj (r j) * eR r = ∏ k, hf (k = i) (k = j) (r k) := by
  simp only [hf, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true, eR]
  rw [← Finset.sum_neg_distrib, Real.exp_sum]
  push_cast
  rfl
end GlobalTheory.CompanionTheory.FSCrofton.GaussDet
