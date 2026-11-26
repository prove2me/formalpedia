-- Prove2me | solution 1 for MohP3.Gen.cert_33
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:07:40.425485+00:00
-- url     : https://prove2.me/submissions/97acc91a-5ab0-4cb7-9fcc-807e386a812c

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
theorem _root_.solution : (162 : A) * (f3 x y z * f3 x y z) =
    (-5*x^3*y + 2*y^2*z) * H1 x y z
    + (-8*x^4 - 13*x*y*z) * H2 x y z := by
  simp only [f1, f2, f3, f4, H1, H2, ell, kappa]
  ring
end MohP3.Gen
