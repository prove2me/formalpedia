-- Prove2me | solution 1 for GlobalTheory.CubeLift.lin_um
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:57:45.147609+00:00
-- url     : https://prove2.me/submissions/8d4756c4-7fe0-4b7e-ac3a-d569b8f491c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Theorems.Thm_GlobalTheory_CubeLift_rd_mv

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
theorem _root_.solution (I : Ideal A) (f : X →+ Y) (u : (A[X])ˣ) : lin I (um f u) = mv f (lin I u) := by
  rw [lin, lin, ← rd_mv, map_sub (mv f), map_one]; rfl
end GlobalTheory.CubeLift
