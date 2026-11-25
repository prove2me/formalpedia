-- Prove2me | solution 1 for HatAffineOffsets.genericTypeI_coverable_offset_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:19:35.155419+00:00
-- url     : https://prove2.me/submissions/5724f582-4d2f-481c-9039-58228f709c35

import Definitions.Def_HatAffineFactorAlignment_FactorAlignment
import Definitions.Def_HatAffineConstantRows_ConstantRows
import Definitions.Def_HatAffineOffsets_TypeI
import Theorems.Thm_HatAffineOffsets_typeI_coverable_offset_count
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
    (A : Fin (Fintype.card K - 1) -> Fin m -> K)
    (lambda : Fin m -> K)
    (b : Fin (Fintype.card K - 1) -> K)
    (F : (Fin m -> K) -> Fin (Fintype.card K - 1) -> K)
    (hI : HatAffineFactorAlignment.GenericTypeI A lambda)
    (hrealize : HatAffineConstantRows.AffineRealizes A b F) :
    (Finset.univ.filter
      (fun x : Fin (Fintype.card K - 1) -> K =>
        OffsetCoverable F x)).card =
      Nat.factorial (Fintype.card K) := by
  classical
  obtain ⟨r, alpha, mu, hmu, halpha, hA, hlambda⟩ := hI
  apply typeI_coverable_offset_count hm hq r alpha b F halpha
  intro y i
  rw [hrealize y i, hA i]
  simp
end HatAffineOffsets
