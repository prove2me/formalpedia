-- Prove2me | solution 1 for HatAffineOffsets.sum_typeII_row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:17:40.332527+00:00
-- url     : https://prove2.me/submissions/dcb0bb47-a6c5-4fe4-9b2c-ae71f455d291

import Definitions.Def_HatAffineOffsets_TypeI
import Definitions.Def_HatAffineOffsets_TypeII
import Theorems.Thm_HatAffineGenericCore_mem_coeffSupport
import Theorems.Thm_HatAffineGenericCore_mem_puncturedValues
import Theorems.Thm_HatAffineGenericCore_puncturedValues_card
attribute [local simp] HatAffineGenericCore.mem_coeffSupport
attribute [local simp] HatAffineGenericCore.mem_puncturedValues
attribute [local simp] HatAffineGenericCore.puncturedValues_card



set_option autoImplicit true
open HatAffineOffsets
universe u
open Finset
attribute [local instance] HatAffineOffsets._p2m_local_instance_68713dd93e_9
namespace HatAffineOffsets
theorem _root_.solution
    {K : Type u} [Field K] {m : Nat}
    (u v : Fin m) (huv : u ≠ v) (alpha c : K) (y : Fin m -> K) :
    (∑ j, (if j = u then alpha else if j = v then -alpha * c else 0) * y j) =
      alpha * (y u - c * y v) := by
  classical
  calc
    (∑ j, (if j = u then alpha else if j = v then -alpha * c else 0) * y j) =
        ∑ j, ((if j = u then alpha * y j else 0) +
          (if j = v then (-alpha * c) * y j else 0)) := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hju : j = u <;> by_cases hjv : j = v <;> simp_all
    _ = alpha * y u + (-alpha * c) * y v := by
      rw [Finset.sum_add_distrib]
      simp
    _ = alpha * (y u - c * y v) := by ring
end HatAffineOffsets
