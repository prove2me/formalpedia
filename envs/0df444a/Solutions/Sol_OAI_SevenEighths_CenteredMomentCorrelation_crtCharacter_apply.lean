-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentCorrelation.crtCharacter_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:09:26.300799+00:00
-- url     : https://prove2.me/submissions/9a62843a-133f-4a74-b05c-9cb8e8681c73

import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Correlation
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Group.Pi.Units
import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_CRT

set_option autoImplicit false
open OAI
open scoped BigOperators Classical
open OAI.SevenEighths OAI.SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {A B : Type*} [CommRing A] [CommRing B] [Fintype A] [Fintype B]
namespace OAI.SevenEighths.CenteredMomentCorrelation
theorem _root_.solution {S ι : Type*} [CommRing S] [Fintype ι] {R : ι → Type*}
    [∀ i, CommRing (R i)] (e : S ≃+* (∀ i, R i)) (χ : ∀ i, MulChar (R i) ℂ) (x : S) :
    crtCharacter e χ x = ∏ i, χ i (e x i) := rfl
end OAI.SevenEighths.CenteredMomentCorrelation
