-- Prove2me | solution 1 for GlobalTheory.CubeLift.rd_mv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:54:41.767811+00:00
-- url     : https://prove2.me/submissions/a79f4017-a1dc-4694-ae47-d89dc390b0a4

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
theorem _root_.solution (I : Ideal A) (f : X →+ Y) (u : A[X]) : rd I (mv f u) = mv f (rd I u) :=
  RingHom.congr_fun (mapRingHom_comp_mapDomainRingHom (Ideal.Quotient.mk I) f) u
end GlobalTheory.CubeLift
