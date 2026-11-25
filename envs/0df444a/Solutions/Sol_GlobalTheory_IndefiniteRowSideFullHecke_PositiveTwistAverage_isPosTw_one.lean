-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.PositiveTwistAverage.isPosTw_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:52:53.523066+00:00
-- url     : https://prove2.me/submissions/add10415-3a83-411a-8a73-8ab05baeedc3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PositiveTwistAverage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.PositiveTwistAverage
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable {P P' A A' : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup P'] [Module ℂ P']
  [AddCommGroup A] [Module ℂ A] [AddCommGroup A'] [Module ℂ A']
variable [MeasurableSpace k] [BorelSpace k]
omit [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.IndefiniteRowSideFullHecke.PositiveTwistAverage
theorem _root_.solution (ψ : AddChar k Circle) (p : ℕ) (π : Representation ℂ (GL n k) P)
    (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ) :
    IsPosTw ψ 1 p π σ b ↔ IsPos ψ p π σ b := by
  simp [IsPosTw, IsPos]
end GlobalTheory.IndefiniteRowSideFullHecke.PositiveTwistAverage
