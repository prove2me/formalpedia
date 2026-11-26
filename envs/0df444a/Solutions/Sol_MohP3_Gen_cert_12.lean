-- Prove2me | solution 1 for MohP3.Gen.cert_12
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:07:12.348795+00:00
-- url     : https://prove2.me/submissions/4a276cff-f3b8-42c1-98b5-0b5a5e57cd5c

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
theorem _root_.solution : (2916 : A) * (f1 x y z * f2 x y z) =
    (-640*x^8*y^4*z^4 + 800*x^7*y^6*z^3 - 250*x^6*y^8*z^2 + 576*x^5*y^5*z^5 - 648*x^4*y^2*z^3 - 225*x^3*y^9*z^3 + 597*x^3*y^4*z^2 - 120*x^2*y^6*z - 54*x^2*y - 324*x*y^8*z^5 + 324*x*y^3*z^4 + 216*y^5*z^3) * H1 x y z
    + (-1024*x^9*y^3*z^4 + 1280*x^8*y^5*z^3 - 400*x^7*y^7*z^2 - 1152*x^6*y^4*z^5 + 2592*x^5*y^6*z^4 - 1170*x^4*y^8*z^3 - 1248*x^4*y^3*z^2 + 780*x^3*y^5*z + 108*x^3 + 648*x^2*y^7*z^5 - 648*x^2*y^2*z^4 - 729*x*y^9*z^4 + 297*x*y^4*z^3 + 486*y^6*z^2 - 486*y*z) * H2 x y z := by
  simp only [f1, f2, f3, f4, H1, H2, ell, kappa]
  ring
end MohP3.Gen
