-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.dslopeIter_comp_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:14:28.345115+00:00
-- url     : https://prove2.me/submissions/f2aaeef8-d031-4793-8260-158fb6d6f0c8

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_RectangleIntegral
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ResidueTheorem
import Theorems.Thm_GroundTheory_Global_Elliptic_swap_dslope_comp_add
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
open scoped Interval Real
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
namespace GroundTheory.Global.Elliptic
theorem _root_.solution (G : ℂ → ℂ) (a w₀ : ℂ) (k : ℕ) :
    dslopeIter w₀ k (fun w ↦ G (w + a)) = fun w ↦ dslopeIter (w₀ + a) k G (w + a) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [dslopeIter_succ', ih, swap_dslope_comp_add]
    funext w
    rw [dslopeIter_succ']
end GroundTheory.Global.Elliptic
