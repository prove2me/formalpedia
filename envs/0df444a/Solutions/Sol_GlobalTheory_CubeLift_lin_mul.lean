-- Prove2me | solution 1 for GlobalTheory.CubeLift.lin_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:01:33.882796+00:00
-- url     : https://prove2.me/submissions/ff72c3e3-56e0-498e-ae84-10ecaf25fede

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Theorems.Thm_GlobalTheory_CubeLift_rd_mul
import Theorems.Thm_P2M_GlobalTheory_CubeLift_mem_cong__73390d79565c

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
    lin I (u * v) = lin I u + lin I v := by
  have := rd_mul (mem_cong'.1 hu) (mem_cong'.1 hv)
  simp only [lin, Units.val_mul, map_sub, map_mul, map_one] at this ⊢
  linear_combination this
end GlobalTheory.CubeLift
