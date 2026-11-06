-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentCorrelation.scaledResidue_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:34:19.266666+00:00
-- url     : https://prove2.me/submissions/f6704b5a-fb0a-4bc7-b84e-bee1b494acc9

import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Correlation
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_FullCorrelation

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators Classical
open OAI.SevenEighths OAI.SevenEighths.CenteredMomentCorrelation
variable {A : Type*} [CommRing A]
namespace OAI.SevenEighths.CenteredMomentCorrelation
theorem _root_.solution (d a m : A) (hm : m = d * a) (x : A) :
    scaledResidue d a m hm (Ideal.Quotient.mk (Ideal.span {d}) x) =
      Ideal.Quotient.mk (Ideal.span {m}) (a * x) := rfl
end OAI.SevenEighths.CenteredMomentCorrelation
