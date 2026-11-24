-- Prove2me | solution 1 for GlobalTheory.SplitFlip.invFourierSum_inv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:55:00.580878+00:00
-- url     : https://prove2.me/submissions/36c91442-60d3-490c-8fc0-f8963f579c9a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Theorems.Thm_GlobalTheory_SplitFlip_invFourierSum_apply

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
theorem _root_.solution (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ) (P : Finset D) (Ψ : Matrix A D k → ℂ)
    (T : Matrix A D k) : invFourierSum ψ⁻¹ ϖ e P Ψ T = if ∀ i, ∀ j ∈ P, T i j ∈ 𝒪[k] then
    ∑ S : A → P → Res k e, Ψ (setCols P T ((ϖ ^ e)⁻¹ • liftRes S)) *
      (ψ (pairCols P T ((ϖ ^ e)⁻¹ • liftRes S)) : ℂ) else 0 := by
  simp only [invFourierSum_apply, AddChar.inv_apply, neg_neg]
end GlobalTheory.SplitFlip
