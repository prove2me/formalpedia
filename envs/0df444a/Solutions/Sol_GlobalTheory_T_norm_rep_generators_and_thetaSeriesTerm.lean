-- Prove2me | solution 1 for GlobalTheory.T.norm_rep_generators_and_thetaSeriesTerm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:04:59.433011+00:00
-- url     : https://prove2.me/submissions/68a8d936-e920-4dd1-87b0-0d1dcd647ef6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormRepGeneratorsAndThetaSeriesTerm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormRepGeneratorsAndThetaSeriesTermStatement
import Theorems.Thm_GlobalTheory_Ex_norm_QT_s_and_norm_txT


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (C : Type) [NormedField C] (N : NumD C) (q : QuadraticMap ℤ N.X ℝ), N.Int q → (∀ (k : ℕ) (p : N.QT k), k ≠ 0 → ∀ χ, ‖(p.1.2.s χ : C)‖ = Real.exp (-(QuadraticMap.polar q p.1.1.toAdd χ / k))) ∧ ∀ (m : ℕ), Odd m → ∀ (p : N.QT (m ^ 2)) χ, ‖N.txT m p χ‖ = Real.exp (-(q (p.1.1.toAdd + m • χ) / (m : ℝ) ^ 2)) * ‖N.th (N.c χ * p.1.2.b ^ m)‖ := by
  first | exact @GlobalTheory.Ex.norm_QT_s_and_norm_txT | exact GlobalTheory.Ex.norm_QT_s_and_norm_txT | (intros; apply GlobalTheory.Ex.norm_QT_s_and_norm_txT <;> assumption)
end _root_.GlobalTheory.T
