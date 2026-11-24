-- Prove2me | solution 1 for GlobalTheory.SplitFlip.splitTheta_fFun_frameFirstBlock_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:08:13.072317+00:00
-- url     : https://prove2.me/submissions/d38b7916-d961-4092-960c-3b713ba1dffa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Theorems.Thm_GlobalTheory_SplitFlip_smallF_mul_left
import Theorems.Thm_GlobalTheory_SplitFlip_exists_secondBlock_of_frameFirstBlock_eq

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
namespace GlobalTheory.SplitFlip
theorem _root_.solution (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ)
    (Ψ : Matrix A' D k → ℂ) (h : GL D k) : fFun μ σ ν Ψ (X0 k σ * (invT h).val) =
      (ν (gdet h) : ℂ) * apow (gdet h) ((Fintype.card D : ℂ) / 2) * smallF μ ν Ψ (Y0 k σ * h.val) := by
  have hX : ∃ h' : GL D k, X0 k σ * (invT h).val = X0 k σ * (invT h').val := ⟨h, rfl⟩
  obtain ⟨C, h1, h2⟩ := exists_secondBlock_of_frameFirstBlock_eq σ hX.choose_spec.symm
  rw [fFun, dif_pos hX, h1, h2, ← smallF_mul_left μ ν Ψ C (Y0 k σ * h.val), map_mul, apow_mul, Units.val_mul]
  ring
end GlobalTheory.SplitFlip
