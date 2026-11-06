-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentCorrelation.common_divisor_frequency
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:28:00.271561+00:00
-- url     : https://prove2.me/submissions/e341b2c3-508b-46c5-b00b-f690f7b45dc3

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
theorem _root_.solution {u v d x y j : A}
    (hdu : d ∣ u) (hdv : d ∣ v) (hcong : u * v ∣ v * x - u * y - j) : d ∣ j := by
  have hleft : d ∣ v * x - u * y := dvd_sub (hdv.trans (dvd_mul_right v x))
    (hdu.trans (dvd_mul_right u y))
  have hprod : d ∣ u * v := hdu.trans (dvd_mul_right u v)
  have hdiff := dvd_sub hleft (hprod.trans hcong)
  convert hdiff using 1 ; ring
end OAI.SevenEighths.CenteredMomentCorrelation
