-- Prove2me | solution 1 for HatAffineOffsets.typeII_coverable_offset_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:26:13.089257+00:00
-- url     : https://prove2.me/submissions/74552b12-b77f-4258-bc9d-326944aa832a

import Definitions.Def_HatAffineOffsets_TypeI
import Definitions.Def_HatAffineOffsets_TypeII
import Theorems.Thm_HatAffineOffsets_typeII_offsetCoverable_iff_good
import Theorems.Thm_HatAffineOffsets_typeIIGood_count
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
    {K : Type u} [Field K] [Fintype K] {m : Nat}
    (hm : 1 <= m) (hq : 4 <= Fintype.card K)
    (u v : Fin m)
    (alpha c b : Fin (Fintype.card K - 1) -> K)
    (F : (Fin m -> K) -> Fin (Fintype.card K - 1) -> K)
    (huv : u ≠ v)
    (halpha : forall i, alpha i ≠ 0)
    (hc : forall i, c i ≠ 0)
    (hsurj : forall z : K, z ≠ 0 -> exists i, c i = z)
    (hrealizeII : forall y i,
      F y i = alpha i * (y u - c i * y v) + b i) :
    (Finset.univ.filter
      (fun x : Fin (Fintype.card K - 1) -> K =>
        OffsetCoverable F x)).card =
      (Fintype.card K) ^ 2 := by
  classical
  let norm := offsetNormalizationEquiv alpha b halpha
  have hsets :
      Finset.univ.filter
          (fun x : Fin (Fintype.card K - 1) -> K => OffsetCoverable F x) =
        Finset.univ.filter
          (fun x : Fin (Fintype.card K - 1) -> K =>
            TypeIIGood c (typeIID alpha b x)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact typeII_offsetCoverable_iff_good hm hq u v alpha c b F huv halpha hc
      hsurj hrealizeII x
  rw [hsets]
  calc
    (Finset.univ.filter
      (fun x : Fin (Fintype.card K - 1) -> K =>
        TypeIIGood c (typeIID alpha b x))).card =
        Fintype.card
          {x : Fin (Fintype.card K - 1) -> K //
            TypeIIGood c (typeIID alpha b x)} :=
      (Fintype.card_subtype _).symm
    _ = Fintype.card
          {d : Fin (Fintype.card K - 1) -> K // TypeIIGood c d} := by
      apply Fintype.card_congr
      apply Equiv.subtypeEquiv norm
      intro x
      rfl
    _ = (Finset.univ.filter
          (fun d : Fin (Fintype.card K - 1) -> K => TypeIIGood c d)).card :=
      Fintype.card_subtype _
    _ = (Fintype.card K) ^ 2 := typeIIGood_count hq c hc hsurj
end HatAffineOffsets
