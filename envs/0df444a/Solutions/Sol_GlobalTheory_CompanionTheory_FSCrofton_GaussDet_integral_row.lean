-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FSCrofton.GaussDet.integral_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:01:37.987693+00:00
-- url     : https://prove2.me/submissions/d4dbc781-ac3e-443b-b74d-ab1e35631feb

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetSquareIntegral
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussDet_integral_hf
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussDet_row_prod

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
theorem _root_.solution (i j : β) :
    ∫ r : β → ℂ, r i * conj (r j) * eR r =
      if i = j then (Real.pi : ℂ) ^ Fintype.card β else 0 := by
  simp_rw [row_prod]
  rw [integral_fintype_prod_volume_eq_prod (fun k : β => hf (k = i) (k = j))]
  simp_rw [integral_hf]
  by_cases h : i = j
  · subst h
    simp
  · rw [if_neg h]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp [h]
end GlobalTheory.CompanionTheory.FSCrofton.GaussDet
