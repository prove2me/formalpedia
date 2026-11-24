-- Prove2me | solution 1 for GlobalTheory.SplitFlip.vecMul_blockScale_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:54:59.76029+00:00
-- url     : https://prove2.me/submissions/12bc59c5-1db2-40ad-83b0-66a361cab61e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Theorems.Thm_GlobalTheory_SplitFlip_mem_stdLat

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
namespace GlobalTheory.SplitFlip
theorem _root_.solution (ϖ : kˣ) (e : ℕ) (P : Finset D) (x : D → k) :
    x ᵥ* (blockScale ϖ e P).val ∈ blockLat ϖ e P ↔ x ∈ stdLat k D := by
  rw [mem_stdLat]
  refine forall_congr' fun j => ?_
  have h0 : 0 < valuation k (blockUnits ϖ e P j : k) := zero_lt_iff.2 (by simp)
  rw [blockScale, diagGL_val, vecMul_diagonal, map_mul, Valuation.mem_integer_iff]
  exact mul_le_iff_le_one_left h0
end GlobalTheory.SplitFlip
