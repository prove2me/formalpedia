-- Prove2me | solution 1 for OAI.SevenEighths.CharacterTransport.primitive_pullback_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:11:43.911829+00:00
-- url     : https://prove2.me/submissions/9ec6d77a-42c8-407b-b7c4-3de81de82501

import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteConductor
import Definitions.Def_OAI_NumberTheory_DirichletL_CharacterTransport
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_apply
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_symm
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_mul
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_primitive_pullback
attribute [local simp] OAI.SevenEighths.CharacterTransport.pullback_apply
attribute [local simp] OAI.SevenEighths.CharacterTransport.pullback_symm
attribute [local simp] OAI.SevenEighths.CharacterTransport.pullback_mul

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CharacterTransport
open SevenEighths.FiniteFourier
noncomputable section
variable {R S : Type*} [CommRing R] [CommRing S]
namespace OAI.SevenEighths.CharacterTransport
theorem _root_.solution (e : R ≃+* S) (χ : MulChar S ℂ) :
    IsPrimitiveOnIdeals (pullback e χ) ↔ IsPrimitiveOnIdeals χ := by
  constructor
  · intro h
    simpa using primitive_pullback e.symm (pullback e χ) h
  · exact primitive_pullback e χ
end OAI.SevenEighths.CharacterTransport
