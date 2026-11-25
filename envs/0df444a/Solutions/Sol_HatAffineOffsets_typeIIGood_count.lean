-- Prove2me | solution 1 for HatAffineOffsets.typeIIGood_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:23:36.117231+00:00
-- url     : https://prove2.me/submissions/ff1653d1-793f-44eb-a77f-cdffe23ea8f6

import Definitions.Def_HatAffineOffsets_TypeI
import Definitions.Def_HatAffineOffsets_TypeII
import Theorems.Thm_HatAffineOffsets_typeIIParam_injective
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
    {K : Type u} [Field K] [Fintype K]
    (hq : 4 <= Fintype.card K)
    (c : Fin (Fintype.card K - 1) -> K)
    (hc : forall i, c i ≠ 0)
    (hsurj : forall z : K, z ≠ 0 -> exists i, c i = z) :
    (Finset.univ.filter
      (fun d : Fin (Fintype.card K - 1) -> K => TypeIIGood c d)).card =
      (Fintype.card K) ^ 2 := by
  classical
  let phi : K × K ->
      {d : Fin (Fintype.card K - 1) -> K // TypeIIGood c d} :=
    fun p => ⟨typeIIParam c p, ⟨p.1, p.2, fun i => rfl⟩⟩
  have hphi : Function.Bijective phi := by
    constructor
    · intro p q hpq
      apply typeIIParam_injective hq c hc hsurj
      exact congrArg Subtype.val hpq
    · intro d
      obtain ⟨a, beta, hd⟩ := d.2
      refine ⟨(a, beta), ?_⟩
      apply Subtype.ext
      funext i
      exact (hd i).symm
  let e : K × K ≃
      {d : Fin (Fintype.card K - 1) -> K // TypeIIGood c d} :=
    Equiv.ofBijective phi hphi
  calc
    (Finset.univ.filter
      (fun d : Fin (Fintype.card K - 1) -> K => TypeIIGood c d)).card =
        Fintype.card
          {d : Fin (Fintype.card K - 1) -> K // TypeIIGood c d} :=
      (Fintype.card_subtype _).symm
    _ = Fintype.card (K × K) := (Fintype.card_congr e).symm
    _ = (Fintype.card K) ^ 2 := by simp [pow_two]
end HatAffineOffsets
