-- Prove2me | solution 1 for GlobalTheory.CubeLift.um_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:57:29.983367+00:00
-- url     : https://prove2.me/submissions/a7d759f0-95f3-40c9-a4eb-25bfab41e1be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Theorems.Thm_GlobalTheory_CubeLift_rd_mv
import Theorems.Thm_GlobalTheory_CubeLift_mem_cong

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
theorem _root_.solution {I : Ideal A} (f : X →+ Y) {u : (A[X])ˣ} (hu : u ∈ cong I) : um f u ∈ cong I :=
  mem_cong.2 ((rd_mv I f u.val).trans (by rw [mem_cong.1 hu, map_one]))
end GlobalTheory.CubeLift
