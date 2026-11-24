-- Prove2me | solution 1 for GlobalTheory.SplitFlip.dualLat_diagLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:06:41.244325+00:00
-- url     : https://prove2.me/submissions/eec49f2f-e25a-4768-a8c2-e6a8a8d98444

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Theorems.Thm_GlobalTheory_SplitFlip_mem_diagLat
import Theorems.Thm_GlobalTheory_SplitFlip_mem_dualLat

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
namespace GlobalTheory.SplitFlip
theorem _root_.solution (c : D → kˣ) : dualLat (diagLat c) = diagLat fun j => (c j)⁻¹ := by
  classical
  have h0 : ∀ j, 0 < valuation k (c j : k) := fun j => zero_lt_iff.2 (by simp)
  ext x
  rw [mem_dualLat, mem_diagLat]
  simp only [Units.val_inv_eq_inv_val, map_inv₀]
  constructor
  · intro h j
    have := h (Pi.single j (c j : k)) fun l => by
      by_cases h : l = j
      · subst h; simp
      · simp [h]
    rw [dotProduct_single, Valuation.mem_integer_iff, map_mul] at this
    rw [← one_mul (valuation k (c j : k))⁻¹]; exact (le_mul_inv_iff₀ (h0 j)).2 this
  · intro h y hy
    refine Subring.sum_mem _ fun j _ => ?_
    rw [Valuation.mem_integer_iff, map_mul]
    exact (mul_le_mul' (h j) (hy j)).trans (inv_mul_cancel₀ (h0 j).ne').le
end GlobalTheory.SplitFlip
