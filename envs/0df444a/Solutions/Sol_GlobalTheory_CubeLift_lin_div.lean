-- Prove2me | solution 1 for GlobalTheory.CubeLift.lin_div
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:03:26.150005+00:00
-- url     : https://prove2.me/submissions/4a944a53-c0fb-4dca-a817-f669c13d44a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Theorems.Thm_GlobalTheory_CubeLift_lin_mul

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
theorem _root_.solution {I : Ideal A} {u v : (A[X])ˣ} (hu : u ∈ cong I) (hv : v ∈ cong I) :
    lin I (u / v) = lin I u - lin I v := by
  rw [eq_sub_iff_add_eq, ← lin_mul (div_mem hu hv) hv, div_mul_cancel]
end GlobalTheory.CubeLift
