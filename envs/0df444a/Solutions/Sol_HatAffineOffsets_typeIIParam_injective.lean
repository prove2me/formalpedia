-- Prove2me | solution 1 for HatAffineOffsets.typeIIParam_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:20:17.487258+00:00
-- url     : https://prove2.me/submissions/56b1adad-02e6-4ff0-96be-c1d426faa2e7

import Definitions.Def_HatAffineOffsets_TypeI
import Definitions.Def_HatAffineOffsets_TypeII
import Theorems.Thm_HatAffineOffsets_typeII_slope_injective
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
    Function.Injective (typeIIParam c) := by
  classical
  have hcinj := typeII_slope_injective hq c hc hsurj
  have hcardI : 1 < Fintype.card (Fin (Fintype.card K - 1)) := by
    simp only [Fintype.card_fin]
    omega
  obtain ⟨i, k, hik⟩ := Fintype.one_lt_card_iff.mp hcardI
  have hcik : c i ≠ c k := fun h => hik (hcinj h)
  intro p q hpq
  have hi := congrFun hpq i
  have hk := congrFun hpq k
  change p.1 - c i * p.2 = q.1 - c i * q.2 at hi
  change p.1 - c k * p.2 = q.1 - c k * q.2 at hk
  have hmul : (c k - c i) * (p.2 - q.2) = 0 := by
    calc
      (c k - c i) * (p.2 - q.2) =
          ((p.1 - c i * p.2) - (p.1 - c k * p.2)) -
            ((q.1 - c i * q.2) - (q.1 - c k * q.2)) := by ring
      _ = 0 := by rw [hi, hk]; ring
  have hb : p.2 = q.2 := by
    have hck : c k - c i ≠ 0 := sub_ne_zero.mpr (Ne.symm hcik)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hck)
  have ha : p.1 = q.1 := by
    calc
      p.1 = (p.1 - c i * p.2) + c i * p.2 := by ring
      _ = (q.1 - c i * q.2) + c i * q.2 := by rw [hi, hb]
      _ = q.1 := by ring
  exact Prod.ext ha hb
end HatAffineOffsets
