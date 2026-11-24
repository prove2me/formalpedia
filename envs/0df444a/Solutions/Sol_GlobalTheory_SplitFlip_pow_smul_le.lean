-- Prove2me | solution 1 for GlobalTheory.SplitFlip.pow_smul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:54:57.323878+00:00
-- url     : https://prove2.me/submissions/40cef20a-f498-40d7-8d2c-dba504be0729

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
variable [Fintype D]
variable [DecidableEq D]
omit [Fintype D] [DecidableEq D]
namespace GlobalTheory.SplitFlip
theorem _root_.solution {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) (Λ : Submodule 𝒪[k] (D → k)) : ϖ ^ e • Λ ≤ Λ := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
  have h : ((ϖ ^ e : kˣ) : k) ∈ 𝒪[k] := by
    rw [Units.val_pow_eq_pow_val]
    exact pow_mem (show valuation k (ϖ : k) ≤ 1 from hϖ ▸ uniformizer_lt_one.le) e
  exact Λ.smul_mem ⟨_, h⟩ hy
end GlobalTheory.SplitFlip
