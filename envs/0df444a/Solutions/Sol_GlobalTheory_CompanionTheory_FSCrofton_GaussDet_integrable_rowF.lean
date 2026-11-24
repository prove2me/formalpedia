-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FSCrofton.GaussDet.integrable_rowF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:19:59.856274+00:00
-- url     : https://prove2.me/submissions/1865cdd8-104e-480e-9f9d-3b9a4afddffd

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetSquareIntegral
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussDet_integrable_row
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussDet_rowF_eq

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
theorem _root_.solution (G : Matrix β (Fin d) ℂ) (a c : Fin d) : Integrable (rowF G a c) := by
  have : rowF G a c = fun r => ∑ i, ∑ j, (G i a * conj (G j c)) * (r i * conj (r j) * eR r) :=
    funext (rowF_eq G a c)
  rw [this]
  exact integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ =>
    (integrable_row i j).const_mul _
end GlobalTheory.CompanionTheory.FSCrofton.GaussDet
