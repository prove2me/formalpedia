-- Prove2me | solution 1 for MohP3.Gen.cert_22
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:07:34.95295+00:00
-- url     : https://prove2.me/submissions/daa28671-0713-4d38-a929-68908f7b836c

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
theorem _root_.solution : (1458 : A) * (f2 x y z * f2 x y z) =
    (-320*x^7*y^5*z^4 + 400*x^6*y^7*z^3 - 125*x^5*y^9*z^2 + 448*x^4*y^6*z^5 - 200*x^3*y^8*z^4 - 224*x^3*y^3*z^3 - 50*x^2*y^10*z^3 + 236*x^2*y^5*z^2 - 144*x*y^7*z^6 - 60*x*y^7*z - 12*x*y^2 - 72*y^9*z^5 + 144*y^4*z^4) * H1 x y z
    + (-512*x^8*y^4*z^4 + 640*x^7*y^6*z^3 - 200*x^6*y^8*z^2 - 320*x^5*y^5*z^5 + 976*x^4*y^7*z^4 + 160*x^4*y^2*z^3 - 485*x^3*y^9*z^3 - 724*x^3*y^4*z^2 + 288*x^2*y^6*z^6 + 390*x^2*y^6*z + 78*x^2*y - 180*x*y^8*z^5 - 288*x*y^3*z^4 - 162*y^10*z^4 + 324*y^5*z^3 - 162*z^2) * H2 x y z := by
  simp only [f1, f2, f3, f4, H1, H2, ell, kappa]
  ring
end MohP3.Gen
