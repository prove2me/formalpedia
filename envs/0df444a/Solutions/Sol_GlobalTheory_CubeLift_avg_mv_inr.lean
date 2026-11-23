-- Prove2me | solution 1 for GlobalTheory.CubeLift.avg_mv_inr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:01:32.952942+00:00
-- url     : https://prove2.me/submissions/9564703c-960e-47ad-bde1-e5d0c5481503

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Theorems.Thm_GlobalTheory_CubeLift_mv_single
import Theorems.Thm_GlobalTheory_CubeLift_avg_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AddMonoidAlgebra
open GlobalTheory GlobalTheory.CubeLift
variable {A : Type} [CommRing A] {X Y W : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup W]
namespace GlobalTheory.CubeLift
theorem _root_.solution (f : W →+ X × Y) (φ : W →+ Y) (h : ∀ w, f w = (0, φ w)) (u : A[W]) :
    avg (mv f u) = mv φ u := by
  induction u using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single p r => rw [mv_single, avg_single, h, mv_single, if_pos rfl]
end GlobalTheory.CubeLift
