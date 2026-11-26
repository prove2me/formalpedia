-- Prove2me | solution 1 for MohP3.Gen.cert_24
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:07:39.673972+00:00
-- url     : https://prove2.me/submissions/09e695f9-ecc1-4259-ab68-c453923e367e

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
theorem _root_.solution : (4374 : A) * (f2 x y z * f4 x y z) =
    (320*x^6*y^5*z^5 - 400*x^5*y^7*z^4 - 160*x^5*y^2*z^3 + 125*x^4*y^9*z^3 + 100*x^4*y^4*z^2 - 288*x^3*y^6*z^6 + 30*x^3*y + 180*x^2*y^8*z^5 + 288*x^2*y^3*z^4 - 216*x*y^5*z^3 - 162*x*z^2 + 108*y^2*z) * H1 x y z
    + (512*x^7*y^4*z^5 - 640*x^6*y^6*z^4 - 256*x^6*y*z^3 + 200*x^5*y^8*z^3 + 160*x^5*y^3*z^2 + 576*x^4*y^5*z^6 + 48*x^4 - 1008*x^3*y^7*z^5 - 576*x^3*y^2*z^4 + 405*x^2*y^9*z^4 + 1080*x^2*y^4*z^3 - 486*x*y^6*z^2 - 216*x*y*z) * H2 x y z := by
  simp only [f1, f2, f3, f4, H1, H2, ell, kappa]
  ring
end MohP3.Gen
