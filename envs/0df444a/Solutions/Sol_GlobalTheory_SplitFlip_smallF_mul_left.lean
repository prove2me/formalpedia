-- Prove2me | solution 1 for GlobalTheory.SplitFlip.smallF_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:32:39.177737+00:00
-- url     : https://prove2.me/submissions/1d420fd4-2d9c-4d64-a8b0-dc4aa7d98a64

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
omit [DecidableEq D]
namespace GlobalTheory.SplitFlip
theorem _root_.solution (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (ν : kˣ →* ℂˣ) (Ψ : Matrix A' D k → ℂ)
    (g₀ : GL A' k) (Y : Matrix A' D k) :
    (ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card D : ℂ) / 2) * smallF μ ν Ψ (g₀.val * Y) = smallF μ ν Ψ Y := by
  unfold smallF
  rw [← integral_mul_right_eq_self (fun g : GL A' k =>
    Ψ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card D : ℂ) / 2)) g₀, ← integral_const_mul]
  congr 1
  funext g
  simp only [Units.val_mul, map_mul, apow_mul, Matrix.mul_assoc]
  ring
end GlobalTheory.SplitFlip
