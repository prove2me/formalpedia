-- Prove2me | solution 1 for HatAffineOffsets.injective_function_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:16:17.373129+00:00
-- url     : https://prove2.me/submissions/b84c809a-f3ff-428b-829e-831a7fc1a5df

import Definitions.Def_HatAffineFactorAlignment_FactorAlignment
import Definitions.Def_HatAffineConstantRows_ConstantRows
import Definitions.Def_HatAffineOffsets_TypeI
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
    {K : Type u} [Fintype K]
    (hq : 1 <= Fintype.card K) :
    (Finset.univ.filter
      (fun f : Fin (Fintype.card K - 1) -> K =>
        Function.Injective f)).card =
      Nat.factorial (Fintype.card K) := by
  classical
  let e :
      {f : Fin (Fintype.card K - 1) -> K // Function.Injective f} ≃
        (Fin (Fintype.card K - 1) ↪ K) :=
    { toFun := fun f => Function.Embedding.mk f.1 f.2
      invFun := fun f => ⟨fun i => f i, f.injective⟩
      left_inv := by
        intro f
        cases f
        rfl
      right_inv := by
        intro f
        cases f
        rfl }
  calc
    (Finset.univ.filter
      (fun f : Fin (Fintype.card K - 1) -> K =>
        Function.Injective f)).card =
        Fintype.card
          {f : Fin (Fintype.card K - 1) -> K // Function.Injective f} :=
      (Fintype.card_subtype _).symm
    _ = Fintype.card (Fin (Fintype.card K - 1) ↪ K) :=
      Fintype.card_congr e
    _ = (Fintype.card K).descFactorial (Fintype.card K - 1) :=
      by
        simpa only [Fintype.card_fin] using
          (Fintype.card_embedding_eq
            (α := Fin (Fintype.card K - 1)) (β := K))
    _ = Nat.factorial (Fintype.card K) := by
      have hle : Fintype.card K - 1 <= Fintype.card K := Nat.sub_le _ _
      have hfac := Nat.factorial_mul_descFactorial hle
      have hone : Fintype.card K - (Fintype.card K - 1) = 1 := by omega
      simpa [hone] using hfac
end HatAffineOffsets
