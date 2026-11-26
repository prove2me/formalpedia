-- Prove2me | solution 1 for MohP3.Gen.cert_44
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:08:20.726656+00:00
-- url     : https://prove2.me/submissions/6c7686da-129e-420c-b9ac-6ca41d15daef

module
public import Mathlib
public import Definitions.Def_MohP3_Generic

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MohP3 MohP3.Gen
variable {A : Type*} [CommRing A]
variable (x y z : A)
namespace MohP3.Gen
theorem _root_.solution : (13122 : A) * (f4 x y z * f4 x y z) =
    (-320*x^5*y^5*z^6 + 400*x^4*y^7*z^5 + 160*x^4*y^2*z^4 - 125*x^3*y^9*z^4 + 140*x^3*y^4*z^3 + 288*x^2*y^6*z^7 - 150*x^2*y^6*z^2 - 30*x^2*y*z - 180*x*y^8*z^6 - 288*x*y^3*z^5 - 180*x*y^3 + 162*z^3) * H1 x y z
    + (-512*x^6*y^4*z^6 + 640*x^5*y^6*z^5 + 256*x^5*y*z^4 - 200*x^4*y^8*z^4 + 224*x^4*y^3*z^3 - 576*x^3*y^5*z^7 - 240*x^3*y^5*z^2 - 48*x^3*z + 1008*x^2*y^7*z^6 + 576*x^2*y^2*z^5 - 288*x^2*y^2 - 405*x*y^9*z^5 - 648*x*y^4*z^4) * H2 x y z := by
  simp only [f1, f2, f3, f4, H1, H2, ell, kappa]
  ring
end MohP3.Gen
