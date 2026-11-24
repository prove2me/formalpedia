-- Prove2me | solution 1 for GlobalTheory.SplitFlip.smallP_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:32:40.104497+00:00
-- url     : https://prove2.me/submissions/234cc9c7-5e49-493a-99bd-ceb669451b11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A A' D : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
variable [MeasurableSpace k] [BorelSpace k]
omit [BorelSpace k] [Fintype A] [DecidableEq A]
namespace GlobalTheory.SplitFlip
theorem _root_.solution (μ : Measure (GL A' k)) (σ : A ⊕ A' ≃ D) (ν α : kˣ →* ℂˣ) (Ψ : Matrix A' D k → ℂ) (h : GL D k) :
    smallP μ σ ν α Ψ h = smallF μ ν (omB ν α 1 h Ψ) (Y0 k σ) := by
  simp [smallP, smallF, omB, Matrix.mul_assoc, mul_assoc, integral_const_mul]
end GlobalTheory.SplitFlip
