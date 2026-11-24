-- Prove2me | solution 1 for GlobalTheory.SplitFlip.smul_diagLat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:48.134305+00:00
-- url     : https://prove2.me/submissions/d76b73db-405f-4da2-a626-18cf79a78ed0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Theorems.Thm_GlobalTheory_SplitFlip_mem_smul_lat
import Theorems.Thm_GlobalTheory_SplitFlip_mem_diagLat

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
namespace GlobalTheory.SplitFlip
theorem _root_.solution (u : kˣ) (c : D → kˣ) : u • diagLat c = diagLat fun j => u * c j := by
  ext x
  rw [mem_smul_lat, mem_diagLat, mem_diagLat]
  refine forall_congr' fun j => ?_
  have h0 : 0 < valuation k (u : k) := zero_lt_iff.2 (by simp)
  simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, Units.val_mul]
  exact inv_mul_le_iff₀ h0
end GlobalTheory.SplitFlip
