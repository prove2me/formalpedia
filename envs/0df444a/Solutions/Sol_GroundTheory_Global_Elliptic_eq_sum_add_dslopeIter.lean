-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.eq_sum_add_dslopeIter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:06:36.395181+00:00
-- url     : https://prove2.me/submissions/1ed1de56-c149-49cd-bbdc-edd29c7dba57

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
import Theorems.Thm_GroundTheory_Global_Elliptic_dslopeIter_zero
import Theorems.Thm_P2M_GroundTheory_Global_Elliptic_dslopeIter_succ__14849de0e418

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
namespace GroundTheory.Global.Elliptic
theorem _root_.solution (p : ℂ) (g : ℂ → ℂ) (k : ℕ) (z : ℂ) :
    g z = ∑ j ∈ Finset.range k, (z - p) ^ j * dslopeIter p j g p +
      (z - p) ^ k * dslopeIter p k g z := by
  induction k with
  | zero => simp [dslopeIter_zero]
  | succ k ih =>
    rw [ih, Finset.sum_range_succ, dslopeIter_succ']
    have h := sub_smul_dslope (dslopeIter p k g) p z
    simp only [smul_eq_mul] at h
    show _ = _ + _ + (z - p) ^ (k + 1) * dslope (dslopeIter p k g) p z
    rw [pow_succ]
    linear_combination -((z - p) ^ k) * h
end GroundTheory.Global.Elliptic
