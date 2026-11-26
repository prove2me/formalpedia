-- Prove2me | solution 1 for MohP3.Gen.cert_13
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:07:17.294459+00:00
-- url     : https://prove2.me/submissions/b9d391a0-de94-4cb1-b1a0-bc87d9d5539c

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
theorem _root_.solution : (972 : A) * (f1 x y z * f3 x y z) =
    (-80*x^6*y^2*z^2 + 50*x^5*y^4*z + 32*x^3*y^3*z^3 + 25*x^2*y^5*z^2 - 81*x^2*z + 54*x*y^2 + 36*y^4*z^4) * H1 x y z
    + (-128*x^7*y*z^2 + 80*x^6*y^3*z - 208*x^4*y^2*z^3 + 202*x^3*y^4*z^2 - 108*x^2*y - 72*x*y^3*z^4 + 81*y^5*z^3 - 81*z^2) * H2 x y z := by
  simp only [f1, f2, f3, f4, H1, H2, ell, kappa]
  ring
end MohP3.Gen
