-- Prove2me | solution 1 for MohP3.Gen.cert_34
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:07:43.772907+00:00
-- url     : https://prove2.me/submissions/29a12dcf-22ea-4565-a1ed-420b121e993a

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
theorem _root_.solution : (1458 : A) * (f3 x y z * f4 x y z) =
    (40*x^4*y^3*z^3 - 25*x^3*y^5*z^2 - 30*x^2*y^2 - 36*x*y^4*z^4 + 18*y*z^2) * H1 x y z
    + (64*x^5*y^2*z^3 - 40*x^4*y^4*z^2 - 48*x^3*y + 72*x^2*y^3*z^4 - 81*x*y^5*z^3 - 36*x*z^2) * H2 x y z := by
  simp only [f1, f2, f3, f4, H1, H2, ell, kappa]
  ring
end MohP3.Gen
