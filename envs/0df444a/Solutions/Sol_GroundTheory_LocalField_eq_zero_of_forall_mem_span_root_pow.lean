-- Prove2me | solution 1 for GroundTheory.LocalField.eq_zero_of_forall_mem_span_root_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:25:35.748404+00:00
-- url     : https://prove2.me/submissions/d8092391-f103-42cf-99f6-61999bd6b0ae

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LubinTateReciprocity_RootEval
import Theorems.Thm_GroundTheory_LocalField_rootEval_X
import Theorems.Thm_GroundTheory_LocalField_rootEval_C
import Theorems.Thm_GroundTheory_LocalField_root_pow_mem_map
import Theorems.Thm_GroundTheory_LocalField_repr_mem_of_mem_map
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.rootEval_X
attribute [local simp] GroundTheory.LocalField.rootEval_C

set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open PowerSeries
variable {B : Type*} [CommRing B] {I : Ideal B} {P : Polynomial B}
namespace GroundTheory.LocalField
theorem _root_.solution [IsHausdorff I B] (hP : P.IsDistinguishedAt I)
    {z : AdjoinRoot P} (hz : ∀ k : ℕ, z ∈ Ideal.span {AdjoinRoot.root P} ^ k) : z = 0 := by
  set pb := AdjoinRoot.powerBasis' hP.monic
  have hmem : ∀ k : ℕ, z ∈ (I ^ k).map (AdjoinRoot.of P) := by
    intro k
    have h := hz (P.natDegree * k)
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
    obtain ⟨w, hw⟩ := h
    rw [hw, pow_mul, Ideal.map_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (root_pow_mem_map hP) k)
  apply pb.basis.repr.injective
  ext i
  rw [map_zero, Finsupp.zero_apply]
  refine IsHausdorff.haus' (I := I) _ fun k => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact repr_mem_of_mem_map hP.monic _ (hmem k) i
end GroundTheory.LocalField
