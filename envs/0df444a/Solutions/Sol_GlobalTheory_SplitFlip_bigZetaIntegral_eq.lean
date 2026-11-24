-- Prove2me | solution 1 for GlobalTheory.SplitFlip.bigZetaIntegral_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:46:35.806158+00:00
-- url     : https://prove2.me/submissions/2b8e5e0b-fdae-4398-b6b5-2cf59f1cfcaf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Theorems.Thm_GlobalTheory_SplitFlip_shellSum_smul

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
omit [BorelSpace k] [Fintype A'] [DecidableEq A']
namespace GlobalTheory.SplitFlip
theorem _root_.solution {a : ℕ} (μ : Measure (GL (Fin a) k)) (ϖ : kˣ) (σ : Fin a ⊕ A' ≃ D) (ν β : kˣ →* ℂˣ)
    (Φ : Matrix (Fin a) D k → ℂ) (h : GL D k) : bigP μ ϖ σ ν β Φ h =
      (β (gdet h) : ℂ) * apow (gdet h) (-(a : ℂ) / 2) * bigF μ ϖ ν Φ (X0 k σ * (invT h).val) := by
  simp [bigP, bigF, omA, ← shellSum_smul, Matrix.mul_assoc]
end GlobalTheory.SplitFlip
