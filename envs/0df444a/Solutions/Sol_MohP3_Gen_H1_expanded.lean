-- Prove2me | solution 1 for MohP3.Gen.H1_expanded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:48:36.530309+00:00
-- url     : https://prove2.me/submissions/c1b48405-a3f6-4d0e-9a84-e967cdea67c8

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
theorem _root_.solution : H1 x y z =
    128*x^7*y*z^3 - 272*x^6*y^3*z^2 - 128*x^5*y^5*z^6
    + 120*x^5*y^5*z - 24*x^5 + 16*x^4*y^7*z^5
    + 208*x^4*y^2*z^4 + 40*x^3*y^9*z^4 - 394*x^3*y^4*z^3
    - 144*x^2*y^6*z^7 + 291*x^2*y^6*z^2 + 177*x^2*y*z
    + 90*x*y^8*z^6 + 144*x*y^3*z^5 - 234*x*y^3
    + 81*y^10*z^5 - 162*y^5*z^4 + 81*z^3 := by
  simp only [H1, f1, f3, f4, ell]
  ring
end MohP3.Gen
