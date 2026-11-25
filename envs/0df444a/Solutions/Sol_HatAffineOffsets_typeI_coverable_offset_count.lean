-- Prove2me | solution 1 for HatAffineOffsets.typeI_coverable_offset_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:18:07.695961+00:00
-- url     : https://prove2.me/submissions/f33bccea-42e2-40f3-ab0e-c1543c04ee01

import Definitions.Def_HatAffineFactorAlignment_FactorAlignment
import Definitions.Def_HatAffineConstantRows_ConstantRows
import Definitions.Def_HatAffineOffsets_TypeI
import Theorems.Thm_HatAffineOffsets_injective_function_count
import Theorems.Thm_HatAffineOffsets_typeI_offsetCoverable_iff_injective
import Theorems.Thm_HatAffineGenericCore_mem_coeffSupport
import Theorems.Thm_HatAffineGenericCore_mem_puncturedValues
import Theorems.Thm_HatAffineGenericCore_puncturedValues_card
attribute [local simp] HatAffineGenericCore.mem_coeffSupport
attribute [local simp] HatAffineGenericCore.mem_puncturedValues
attribute [local simp] HatAffineGenericCore.puncturedValues_card



set_option autoImplicit true
open HatAffineOffsets
universe u v w
open Finset
attribute [local instance] HatAffineOffsets._p2m_local_instance_8d02a9c2cf_10
namespace HatAffineOffsets
theorem _root_.solution
    {K : Type u} [Field K] [Fintype K] {m : Nat}
    (hm : 1 <= m) (hq : 4 <= Fintype.card K)
    (r : Fin m)
    (alpha b : Fin (Fintype.card K - 1) -> K)
    (F : (Fin m -> K) -> Fin (Fintype.card K - 1) -> K)
    (halpha : forall i, alpha i ≠ 0)
    (hrealizeI : forall y i, F y i = alpha i * y r + b i) :
    (Finset.univ.filter
      (fun x : Fin (Fintype.card K - 1) -> K =>
        OffsetCoverable F x)).card =
      Nat.factorial (Fintype.card K) := by
  classical
  let e := offsetNormalizationEquiv alpha b halpha
  have hsets :
      Finset.univ.filter
          (fun x : Fin (Fintype.card K - 1) -> K => OffsetCoverable F x) =
        Finset.univ.filter
          (fun x : Fin (Fintype.card K - 1) -> K =>
            Function.Injective (typeIRoot alpha b x)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact typeI_offsetCoverable_iff_injective
      hm hq r alpha b F halpha hrealizeI x
  rw [hsets]
  calc
    (Finset.univ.filter
      (fun x : Fin (Fintype.card K - 1) -> K =>
        Function.Injective (typeIRoot alpha b x))).card =
        Fintype.card
          {x : Fin (Fintype.card K - 1) -> K //
            Function.Injective (typeIRoot alpha b x)} :=
      (Fintype.card_subtype _).symm
    _ = Fintype.card
          {d : Fin (Fintype.card K - 1) -> K // Function.Injective d} := by
      apply Fintype.card_congr
      apply Equiv.subtypeEquiv e
      intro x
      rfl
    _ = (Finset.univ.filter
          (fun d : Fin (Fintype.card K - 1) -> K =>
            Function.Injective d)).card :=
      Fintype.card_subtype _
    _ = Nat.factorial (Fintype.card K) :=
      injective_function_count (by omega)
end HatAffineOffsets
