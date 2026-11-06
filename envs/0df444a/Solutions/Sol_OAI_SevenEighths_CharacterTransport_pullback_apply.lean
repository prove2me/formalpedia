-- Prove2me | solution 1 for OAI.SevenEighths.CharacterTransport.pullback_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:34:41.696205+00:00
-- url     : https://prove2.me/submissions/dd7521a8-42f1-48d1-bc9a-f0932e83afd5

import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteConductor
import Definitions.Def_OAI_NumberTheory_DirichletL_CharacterTransport

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CharacterTransport
open SevenEighths.FiniteFourier
noncomputable section
variable {R S : Type*} [CommRing R] [CommRing S]
namespace OAI.SevenEighths.CharacterTransport
theorem _root_.solution (e : R ≃+* S) (χ : MulChar S ℂ) (x : R) :
    pullback e χ x = χ (e x) := rfl
end OAI.SevenEighths.CharacterTransport
