-- Prove2me | solution 1 for OAI.SevenEighths.CharacterTransport.pullback_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:39:28.495671+00:00
-- url     : https://prove2.me/submissions/609e126e-fb60-4752-ade1-ae655f778f58

import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteConductor
import Definitions.Def_OAI_NumberTheory_DirichletL_CharacterTransport
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_apply
attribute [local simp] OAI.SevenEighths.CharacterTransport.pullback_apply

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CharacterTransport
open SevenEighths.FiniteFourier
noncomputable section
variable {R S : Type*} [CommRing R] [CommRing S]
namespace OAI.SevenEighths.CharacterTransport
theorem _root_.solution (e : R ≃+* S) (χ : MulChar S ℂ) :
    pullback e.symm (pullback e χ) = χ := by
  apply MulChar.ext'
  intro x
  simp
end OAI.SevenEighths.CharacterTransport
