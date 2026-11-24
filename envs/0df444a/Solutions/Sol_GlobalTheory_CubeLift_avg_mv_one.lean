-- Prove2me | solution 1 for GlobalTheory.CubeLift.avg_mv_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:02:52.101773+00:00
-- url     : https://prove2.me/submissions/f6e06775-fce5-4b21-be1c-0918f27f711d

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
theorem _root_.solution (f : X →+ X × Y) (h : ∀ a, (f a).1 = a) (u : A[X]) :
    avg (mv f u) = single 0 (u.coeff 0) := by
  induction u using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb, coeff_add, Finsupp.add_apply, single_add]
  | single p r =>
    rw [mv_single, avg_single, h]
    split_ifs with hp
    · subst hp; simp
    · simp [hp]
end GlobalTheory.CubeLift
