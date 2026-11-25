-- Prove2me | solution 1 for HatAffineOffsets.puncturedLine_card_eq_allowed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:17:08.909531+00:00
-- url     : https://prove2.me/submissions/31a8a315-f0d1-4c01-9881-eecfd865c4da

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
    {K : Type u} [Field K] [Fintype K]
    (c e : K) :
    (puncturedLine c e).card = (allowedLineParameter c e).card := by
  classical
  let lineEquiv :
      {p : K × K // p ∈ puncturedLine c e} ≃
        {t : K // t ∈ allowedLineParameter c e} :=
    { toFun := fun p => by
        have hp := Finset.mem_filter.mp p.2
        have hpP := Finset.mem_product.mp hp.1
        have hs0 : p.1.1 ≠ 0 := by
          simpa [nonzeroFinset] using hpP.1
        have ht : p.1.2 ∈ nonzeroFinset K := hpP.2
        have hs : p.1.1 = c * p.1.2 + e := by
          calc
            p.1.1 = (p.1.1 - c * p.1.2) + c * p.1.2 := by ring
            _ = e + c * p.1.2 := by rw [hp.2]
            _ = c * p.1.2 + e := by ring
        have hct : c * p.1.2 + e ≠ 0 := by
          rw [← hs]
          exact hs0
        exact ⟨p.1.2, Finset.mem_filter.mpr ⟨ht, hct⟩⟩
      invFun := fun t => by
        have ht := Finset.mem_filter.mp t.2
        refine ⟨(c * t.1 + e, t.1), Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
        · apply Finset.mem_product.mpr
          exact ⟨by simpa [nonzeroFinset] using ht.2, ht.1⟩
        · ring
      left_inv := by
        intro p
        apply Subtype.ext
        apply Prod.ext
        · have hp := Finset.mem_filter.mp p.2
          calc
            c * p.1.2 + e = c * p.1.2 + (p.1.1 - c * p.1.2) := by rw [hp.2]
            _ = p.1.1 := by ring
        · rfl
      right_inv := by
        intro t
        apply Subtype.ext
        rfl }
  simpa using Fintype.card_congr lineEquiv
end HatAffineOffsets
