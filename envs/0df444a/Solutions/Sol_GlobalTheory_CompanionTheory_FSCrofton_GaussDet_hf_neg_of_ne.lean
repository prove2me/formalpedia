-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FSCrofton.GaussDet.hf_neg_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:30:03.379929+00:00
-- url     : https://prove2.me/submissions/6be9f580-1845-4116-b187-16be0dd572e1

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
namespace GlobalTheory.CompanionTheory.FSCrofton.GaussDet
theorem _root_.solution (p q : Prop) [Decidable p] [Decidable q] (h : ¬ (p ↔ q)) (z : ℂ) :
    hf p q (-z) = - hf p q z := by
  unfold hf
  by_cases hp : p <;> by_cases hq : q <;> simp_all
end GlobalTheory.CompanionTheory.FSCrofton.GaussDet
