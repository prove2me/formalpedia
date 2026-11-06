-- Prove2me | solution 1 for OAI.SevenEighths.IdealCharacter.ofResidue_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T04:58:43.465199+00:00
-- url     : https://prove2.me/submissions/0df21a34-80f2-4dfa-a9ee-f375f3c657a1

import Definitions.Def_OAI_NumberTheory_DirichletL_ResidueCharacter
import Mathlib.RingTheory.PrincipalIdealDomain
import Definitions.Def_OAI_NumberTheory_DirichletL_IdealCharacter

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.IdealCharacter
open SevenEighths.FiniteFourier SevenEighths.FiniteConductor
open SevenEighths.ConductorPresentation
open Submodule.IsPrincipal
open scoped Classical
noncomputable section
variable {A : Type*} [CommRing A]
variable [IsDomain A] [IsPrincipalIdealRing A]
namespace OAI.SevenEighths.IdealCharacter
theorem _root_.solution (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ)
    (hχ : UnitInvariant M χ) : ofResidue M χ hχ ⊥ = 0 := value_bot M χ
end OAI.SevenEighths.IdealCharacter
