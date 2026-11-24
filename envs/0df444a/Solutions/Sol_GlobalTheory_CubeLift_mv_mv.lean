-- Prove2me | solution 1 for GlobalTheory.CubeLift.mv_mv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:02:35.952842+00:00
-- url     : https://prove2.me/submissions/9b8b6cdf-6d8a-41ef-abc2-87f24db86770

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd

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
theorem _root_.solution (g : Y →+ W) (f : X →+ Y) (u : A[X]) : mv g (mv f u) = mv (g.comp f) u := by
  simp [mv, mapDomainRingHom_comp]
end GlobalTheory.CubeLift
