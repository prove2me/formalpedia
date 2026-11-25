-- Prove2me | solution 1 for HatAffineFullTheorem.all_offsetCoverable_count_of_extends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:18:42.167214+00:00
-- url     : https://prove2.me/submissions/6222a55b-300c-4f85-a295-d6964be44ecb

import Definitions.Def_HatAffineFullTheorem_LeadingClassification
import Definitions.Def_HatAffineOffsets_TypeI
import Definitions.Def_HatAffineOffsets_TypeII
import Definitions.Def_HatAffineFullTheorem_GeneralNoGo
import Theorems.Thm_HatAffineGeneral_extends_iff_coverable
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
    {K : Type u} [Field K] [Fintype K] {m : Nat}
    (F : (Fin m → K) → Fin (Fintype.card K - 1) → K)
    (hext : HatAffineGeneral.Extends F) :
    (Finset.univ.filter
      (fun x : Fin (Fintype.card K - 1) → K =>
        HatAffineOffsets.OffsetCoverable F x)).card =
      (Fintype.card K) ^ (Fintype.card K - 1) := by
  classical
  have hall : ∀ x : Fin (Fintype.card K - 1) → K,
      HatAffineOffsets.OffsetCoverable F x := by
    intro x
    simpa only [HatAffineOffsets.OffsetCoverable] using
      (HatAffineGeneral.extends_iff_coverable F).mp hext x
  have hfilter :
      Finset.univ.filter
          (fun x : Fin (Fintype.card K - 1) → K =>
            HatAffineOffsets.OffsetCoverable F x) =
        Finset.univ := by
    ext x
    simp [hall x]
  rw [hfilter, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
end HatAffineFullTheorem
