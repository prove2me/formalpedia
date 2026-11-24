-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FSCrofton.GaussDet.continuous_hf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:30:02.633623+00:00
-- url     : https://prove2.me/submissions/e2ac0a4b-bed5-45d7-95a2-d237fedb7991

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
theorem _root_.solution (p q : Prop) [Decidable p] [Decidable q] : Continuous (hf p q) := by
  unfold hf
  by_cases hp : p <;> by_cases hq : q <;> simp only [hp, hq, if_true, if_false] <;> fun_prop
end GlobalTheory.CompanionTheory.FSCrofton.GaussDet
