-- Prove2me | solution 1 for GlobalTheory.MulCocycle.mem_map_algebraMap_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:59:26.541374+00:00
-- url     : https://prove2.me/submissions/11db360d-9de2-426f-a8d3-07a36045c0c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUnitCoboundaryOfMulCocycle
import Theorems.Thm_GlobalTheory_coe_unitsAddMonoidAlgebraEquiv
import Theorems.Thm_GlobalTheory_mem_coactionWeightSpace
import Theorems.Thm_GlobalTheory_trivialCoaction_apply
import Theorems.Thm_GlobalTheory_tupleCoface_last
import Theorems.Thm_GlobalTheory_tupleCoface_zero
import Theorems.Thm_GlobalTheory_tupleContraction_apply
import Theorems.Thm_P2M_GlobalTheory_hochschildD__trivialCoaction_d0af9f793cf0
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_unitsAddMonoidAlgebraEquiv
attribute [local simp] GlobalTheory.mem_coactionWeightSpace
attribute [local simp] GlobalTheory.trivialCoaction_apply
attribute [local simp] GlobalTheory.tupleCoface_last
attribute [local simp] GlobalTheory.tupleCoface_zero
attribute [local simp] GlobalTheory.tupleContraction_apply
attribute [local simp] P2M_GlobalTheory_hochschildD__trivialCoaction_d0af9f793cf0



set_option autoImplicit false
set_option autoImplicit false
open AddMonoidAlgebra
open GlobalTheory GlobalTheory.MulCocycle
variable {B : Type*} [CommRing B] {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
namespace GlobalTheory.MulCocycle
theorem _root_.solution (J : Ideal B) (b : B[X]) :
    b ∈ J.map (algebraMap B B[X]) ↔ ∀ x, b.coeff x ∈ J := by
  constructor
  · intro hb
    have hb' : b ∈ J • (⊤ : Submodule B B[X]) := by
      rw [Ideal.smul_top_eq_map]; exact hb
    refine Submodule.smul_induction_on hb' (p := fun b => ∀ x, b.coeff x ∈ J) ?_ ?_
    · intro r hr m _ x
      simpa using J.mul_mem_right _ hr
    · intro m m' h h' x
      simpa using J.add_mem (h x) (h' x)
  · intro h
    rw [← AddMonoidAlgebra.sum_coeff_single b]
    refine Ideal.sum_mem _ fun x _ => ?_
    have : single x (b.coeff x) = single x 1 * algebraMap B B[X] (b.coeff x) := by
      simp [AddMonoidAlgebra.single_mul_single]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (h x))
end GlobalTheory.MulCocycle
