-- Prove2me | solution 1 for GlobalTheory.CubeLift.rd_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:56:28.288471+00:00
-- url     : https://prove2.me/submissions/c93e1e43-33aa-4a46-b391-db8dc2c8b974

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
theorem _root_.solution {I I' : Ideal A} {u v : A[X]} (hu : rd I u = 0) (hv : rd I' v = 0) : rd (I * I') (u * v) = 0 := by
  classical
  rw [rd_eq_zero] at *
  intro x
  rw [coeff_mul]
  refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
  dsimp only
  split_ifs
  · exact Ideal.mul_mem_mul (hu a) (hv b)
  · exact zero_mem _
end GlobalTheory.CubeLift
