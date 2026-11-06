-- Prove2me | solution 1 for OAI.SevenEighths.FiniteConductor.quotientComapEquiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:11:23.465457+00:00
-- url     : https://prove2.me/submissions/f9cdd225-c90b-4669-ae4c-60fc51f6d9b5

import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteConductor
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorBounds

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.FiniteConductor
open SevenEighths.FiniteFourier
open scoped Classical
noncomputable section
variable {R : Type*} [CommRing R]
namespace OAI.SevenEighths.FiniteConductor
theorem _root_.solution (M : Ideal R) (I : Ideal (R ⧸ M)) (a : R) :
    quotientComapEquiv M I (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk I (Ideal.Quotient.mk M a) := rfl
end OAI.SevenEighths.FiniteConductor
