-- Prove2me | solution 1 for GlobalTheory.CubeLift.rd_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:56:27.966214+00:00
-- url     : https://prove2.me/submissions/4f9c063c-3428-47f4-b1d6-df9aeed736d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Theorems.Thm_GlobalTheory_CubeLift_rd_eq_zero

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
theorem _root_.solution {I I' : Ideal A} (h : I ≤ I') {u : A[X]} (hu : rd I u = 0) : rd I' u = 0 :=
  rd_eq_zero.2 fun x => h (rd_eq_zero.1 hu x)
end GlobalTheory.CubeLift
