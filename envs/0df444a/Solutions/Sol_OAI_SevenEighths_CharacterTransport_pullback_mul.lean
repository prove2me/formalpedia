-- Prove2me | solution 1 for OAI.SevenEighths.CharacterTransport.pullback_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:40:49.019592+00:00
-- url     : https://prove2.me/submissions/ee1a7221-b078-49a6-81fd-25eed19b8211

import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteConductor
import Definitions.Def_OAI_NumberTheory_DirichletL_CharacterTransport
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_apply
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_symm
attribute [local simp] OAI.SevenEighths.CharacterTransport.pullback_apply
attribute [local simp] OAI.SevenEighths.CharacterTransport.pullback_symm

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CharacterTransport
open SevenEighths.FiniteFourier
noncomputable section
variable {R S : Type*} [CommRing R] [CommRing S]
namespace OAI.SevenEighths.CharacterTransport
theorem _root_.solution (e : R ≃+* S) (χ ψ : MulChar S ℂ) :
    pullback e (χ * ψ) = pullback e χ * pullback e ψ := by
  apply MulChar.ext'
  intro x
  rfl
end OAI.SevenEighths.CharacterTransport
