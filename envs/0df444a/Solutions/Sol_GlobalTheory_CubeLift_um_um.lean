-- Prove2me | solution 1 for GlobalTheory.CubeLift.um_um
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:20:54.610844+00:00
-- url     : https://prove2.me/submissions/f4ddff06-c037-43d9-a442-a5348e7c0350

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Theorems.Thm_GlobalTheory_CubeLift_mv_mv

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
theorem _root_.solution (g : Y →+ W) (f : X →+ Y) (u : (A[X])ˣ) : um g (um f u) = um (g.comp f) u :=
  Units.ext (mv_mv g f u.val)
end GlobalTheory.CubeLift
