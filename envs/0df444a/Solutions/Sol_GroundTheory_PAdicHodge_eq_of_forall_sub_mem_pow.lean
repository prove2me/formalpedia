-- Prove2me | solution 1 for GroundTheory.PAdicHodge.eq_of_forall_sub_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:32.956964+00:00
-- url     : https://prove2.me/submissions/a2f5055b-8bc1-4f94-9dbc-2a71ca7f9a27

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BdRSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open PowerSeries
variable {B : Type*} [CommRing B] (I : Ideal B)
namespace GroundTheory.PAdicHodge
theorem _root_.solution [IsHausdorff I B] {x y : B} (h : ∀ n, x - y ∈ I ^ n) : x = y := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (inferInstance : IsHausdorff I B) (x - y) fun n => ?_
  rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
  exact h n
end GroundTheory.PAdicHodge
