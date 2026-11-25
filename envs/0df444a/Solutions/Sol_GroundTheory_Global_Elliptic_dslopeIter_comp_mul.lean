-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.dslopeIter_comp_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:13:39.924799+00:00
-- url     : https://prove2.me/submissions/df3c3354-8711-443d-83a9-2667e7532ec4

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
import Theorems.Thm_GroundTheory_Global_Elliptic_dslopeIter_zero
import Theorems.Thm_P2M_GroundTheory_Global_Elliptic_dslopeIter_succ__14849de0e418
import Theorems.Thm_GroundTheory_Global_Elliptic_analyticAt_dslopeIter
import Theorems.Thm_GroundTheory_Global_Elliptic_swap_dslope_const_mul
import Theorems.Thm_GroundTheory_Global_Elliptic_swap_dslope_comp_mul

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
theorem _root_.solution {G : ℂ → ℂ} {c w₀ : ℂ} (hc : c ≠ 0) (hG : AnalyticAt ℂ G (c * w₀))
    (k : ℕ) :
    dslopeIter w₀ k (fun w ↦ G (c * w)) = fun w ↦ c ^ k * dslopeIter (c * w₀) k G (c * w) := by
  induction k with
  | zero => funext w; simp [dslopeIter_zero]
  | succ k ih =>
    rw [dslopeIter_succ', ih]
    rw [swap_dslope_const_mul w₀ (c ^ k) (fun w ↦ dslopeIter (c * w₀) k G (c * w))]
    rw [swap_dslope_comp_mul hc ((analyticAt_dslopeIter hG k).differentiableAt)]
    funext w
    rw [dslopeIter_succ']
    ring
end GroundTheory.Global.Elliptic
