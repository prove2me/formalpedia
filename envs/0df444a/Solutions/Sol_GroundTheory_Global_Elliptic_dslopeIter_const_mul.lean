-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.dslopeIter_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:06:34.808119+00:00
-- url     : https://prove2.me/submissions/dcd90bab-6260-4a05-a987-fb9a2451236f

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
import Theorems.Thm_P2M_GroundTheory_Global_Elliptic_dslopeIter_succ__14849de0e418
import Theorems.Thm_GroundTheory_Global_Elliptic_swap_dslope_const_mul

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
theorem _root_.solution (p a : ℂ) (g : ℂ → ℂ) (k : ℕ) :
    dslopeIter p k (fun z ↦ a * g z) = fun z ↦ a * dslopeIter p k g z := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [dslopeIter_succ', ih, swap_dslope_const_mul, dslopeIter_succ']
end GroundTheory.Global.Elliptic
