-- Prove2me | solution 1 for MohP3.Gen.cert_14
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:07:26.148737+00:00
-- url     : https://prove2.me/submissions/4c56a96e-1324-4d97-ae8f-420de3d853e6

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
theorem _root_.solution : (8748 : A) * (f1 x y z * f4 x y z) =
    (640*x^7*y^4*z^5 - 800*x^6*y^6*z^4 + 250*x^5*y^8*z^3 - 480*x^5*y^3*z^2 - 576*x^4*y^5*z^6 + 300*x^4*y^5*z + 648*x^3*y^2*z^4 + 225*x^2*y^9*z^4 - 405*x^2*y^4*z^3 + 270*x*y^6*z^2 - 432*x*y*z + 324*y^8*z^6 - 324*y^3*z^5 + 324*y^3) * H1 x y z
    + (1024*x^8*y^3*z^5 - 1280*x^7*y^5*z^4 + 400*x^6*y^7*z^3 - 768*x^6*y^2*z^2 + 1152*x^5*y^4*z^6 + 480*x^5*y^4*z - 2592*x^4*y^6*z^5 + 1170*x^3*y^8*z^4 + 432*x^2*y^5*z^2 - 108*x^2*z - 648*x*y^7*z^6 + 648*x*y^2*z^5 - 648*x*y^2 + 729*y^9*z^5 - 729*y^4*z^4) * H2 x y z := by
  simp only [f1, f2, f3, f4, H1, H2, ell, kappa]
  ring
end MohP3.Gen
