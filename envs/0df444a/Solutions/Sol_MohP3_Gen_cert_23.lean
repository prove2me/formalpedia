-- Prove2me | solution 1 for MohP3.Gen.cert_23
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:07:36.317809+00:00
-- url     : https://prove2.me/submissions/076745c4-9dac-452d-b6f2-32d373064b31

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
theorem _root_.solution : (486 : A) * (f2 x y z * f3 x y z) =
    (-40*x^5*y^3*z^2 + 25*x^4*y^5*z + 36*x^2*y^4*z^3 - 18*x*y*z + 12*y^3) * H1 x y z
    + (-64*x^6*y^2*z^2 + 40*x^5*y^4*z - 72*x^3*y^3*z^3 + 81*x^2*y^5*z^2 + 36*x^2*z - 78*x*y^2) * H2 x y z := by
  simp only [f1, f2, f3, f4, H1, H2, ell, kappa]
  ring
end MohP3.Gen
