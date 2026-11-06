-- Prove2me | solution 1 for OAI.SevenEighths.RayQuotient.toFullRay_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:01:13.663722+00:00
-- url     : https://prove2.me/submissions/84d02b8e-217a-4765-85ba-047ad37d19cc

import Definitions.Def_OAI_NumberTheory_DirichletL_RayOrthogonality
import Definitions.Def_OAI_NumberTheory_DirichletL_RayQuotient

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.RayQuotient
open SevenEighths.RayOrthogonality
open scoped Classical
noncomputable section
variable {A : Type*} [CommRing A] (M : Ideal A) [Finite (A ⧸ M)]
    (H : Subgroup (A ⧸ M)ˣ) (hH : globalUnits M ≤ H)
include hH
namespace OAI.SevenEighths.RayQuotient
theorem _root_.solution : Function.Injective (toFullRay M H hH) := by
  intro χ ψ heq
  exact Subtype.ext (congrArg (fun ρ : rayCharacters M => (ρ : MulChar (A ⧸ M) ℂ)) heq)
end OAI.SevenEighths.RayQuotient
