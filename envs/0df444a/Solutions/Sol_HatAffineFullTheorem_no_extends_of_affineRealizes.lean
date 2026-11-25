-- Prove2me | solution 1 for HatAffineFullTheorem.no_extends_of_affineRealizes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:41:49.712948+00:00
-- url     : https://prove2.me/submissions/7e8e9218-c99e-413c-98d3-8279cfb10999

import Definitions.Def_HatAffineFullTheorem_LeadingClassification
import Definitions.Def_HatAffineOffsets_TypeI
import Definitions.Def_HatAffineOffsets_TypeII
import Definitions.Def_HatAffineFullTheorem_GeneralNoGo
import Theorems.Thm_HatAffineFullTheorem_all_offsetCoverable_count_of_extends
import Theorems.Thm_HatAffineFullTheorem_factorial_card_lt_total_offsets
import Theorems.Thm_HatAffineFullTheorem_square_card_lt_total_offsets
import Theorems.Thm_HatAffineFullTheorem_affine_factor_alignment_of_extends
import Theorems.Thm_HatAffineOffsets_genericTypeII_coverable_offset_count
import Theorems.Thm_HatAffineOffsets_genericTypeI_coverable_offset_count


set_option autoImplicit true
open scoped BigOperators
open HatAffineFullTheorem
universe u
attribute [local instance] HatAffineFullTheorem._p2m_local_instance_f43eda1e4a_11
namespace HatAffineFullTheorem
theorem _root_.solution
    {K : Type u} [Field K] [Fintype K] {m : Nat}
    (hm : 1 ≤ m) (hq : 4 ≤ Fintype.card K)
    (A : Fin (Fintype.card K - 1) → Fin m → K)
    (b : Fin (Fintype.card K - 1) → K)
    (F :
      (Fin m → K) →
      Fin (Fintype.card K - 1) → K)
    (hrealize : HatAffineConstantRows.AffineRealizes A b F) :
    ¬ HatAffineGeneral.Extends F := by
  intro hext
  obtain ⟨lambda, hI | hII⟩ :=
    affine_factor_alignment_of_extends hm hq A b F hrealize hext
  · have hall := all_offsetCoverable_count_of_extends F hext
    have hcount :=
      HatAffineOffsets.genericTypeI_coverable_offset_count
        hm hq A lambda b F hI hrealize
    have hstrict :=
      factorial_card_lt_total_offsets (Fintype.card K) hq
    omega
  · have hall := all_offsetCoverable_count_of_extends F hext
    have hcount :=
      HatAffineOffsets.genericTypeII_coverable_offset_count
        hm hq A lambda b F hII hrealize
    have hstrict :=
      square_card_lt_total_offsets (Fintype.card K) hq
    omega
end HatAffineFullTheorem
