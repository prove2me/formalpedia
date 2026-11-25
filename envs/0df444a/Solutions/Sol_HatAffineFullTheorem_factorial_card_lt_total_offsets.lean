-- Prove2me | solution 1 for HatAffineFullTheorem.factorial_card_lt_total_offsets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:18:54.546798+00:00
-- url     : https://prove2.me/submissions/71f981d7-ae7d-4145-9296-1ef4458681a1

import Definitions.Def_HatAffineFullTheorem_LeadingClassification
import Definitions.Def_HatAffineOffsets_TypeI
import Definitions.Def_HatAffineOffsets_TypeII
import Definitions.Def_HatAffineFullTheorem_GeneralNoGo
import Theorems.Thm_HatAffineGenericCore_mem_coeffSupport
import Theorems.Thm_HatAffineGenericCore_mem_puncturedValues
import Theorems.Thm_HatAffineGenericCore_puncturedValues_card
attribute [local simp] HatAffineGenericCore.mem_coeffSupport
attribute [local simp] HatAffineGenericCore.mem_puncturedValues
attribute [local simp] HatAffineGenericCore.puncturedValues_card



set_option autoImplicit true
open scoped BigOperators
open HatAffineFullTheorem
universe u
attribute [local instance] HatAffineFullTheorem._p2m_local_instance_f43eda1e4a_11
namespace HatAffineFullTheorem
theorem _root_.solution
    (q : Nat) (hq : 4 ≤ q) :
    Nat.factorial q < q ^ (q - 1) := by
  induction q, hq using Nat.le_induction with
  | base => norm_num [Nat.factorial]
  | succ q hq ih =>
      calc
        Nat.factorial (q + 1) = (q + 1) * Nat.factorial q := by
          rw [Nat.factorial_succ]
        _ < (q + 1) * q ^ (q - 1) :=
          Nat.mul_lt_mul_of_pos_left ih (by omega)
        _ ≤ (q + 1) * (q + 1) ^ (q - 1) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left q.le_succ _)
        _ = (q + 1) ^ ((q + 1) - 1) := by
          simp only [Nat.add_sub_cancel]
          rw [show q = (q - 1) + 1 by omega, pow_succ]
          exact Nat.mul_comm _ _
end HatAffineFullTheorem
