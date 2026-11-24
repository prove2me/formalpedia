-- Prove2me | solution 1 for GlobalTheory.SplitFlip.fourierSum_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:14.664495+00:00
-- url     : https://prove2.me/submissions/2735cf5c-dadd-4b6d-8861-ea5fac66b3a8

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
variable {A D : Type*}
variable [DecidableEq D]
variable [Fintype A]
variable [DecidableEq A]
open Classical
namespace GlobalTheory.SplitFlip
theorem _root_.solution (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ) (P : Finset D) (Φ : Matrix A D k → ℂ)
    (Y : Matrix A D k) : fourierSum ψ ϖ e P Φ Y = if ∀ i, ∀ j ∈ P, ((ϖ ^ e : kˣ) : k) * Y i j ∈ 𝒪[k] then
    ((resCard k : ℂ) ^ (e * Fintype.card A * P.card))⁻¹ *
      ∑ T : A → P → Res k e, Φ (setCols P Y (liftRes T)) * (ψ (pairCols P Y (liftRes T)) : ℂ) else 0 := rfl
end GlobalTheory.SplitFlip
