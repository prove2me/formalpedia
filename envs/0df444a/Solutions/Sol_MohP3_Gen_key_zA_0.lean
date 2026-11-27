-- Prove2me | solution 1 for MohP3.Gen.key_zA_0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:22:44.06795+00:00
-- url     : https://prove2.me/submissions/d75788d6-3d17-4474-a909-7f6cadcd4d10

module
public import Definitions.Def_MohP3_Generic
public import Definitions.Def_MohP3_GenClosure

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MohP3 MohP3.Gen
variable {A : Type*} [CommRing A]
variable (x y z : A)
namespace MohP3.Gen
theorem _root_.solution :
    (18 : A) * (z * hh x y z 0) =
      (∑ j, qzA y 0 j * hh x y z j) + ∑ j, wzA x y z 0 j * ff x y z j := by
  simp only [hh, ff, qzA, wzA, qzD, wzD, f1, f2, f3, f4, Fin.sum_univ_eight,
    Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Int.cast_zero, Int.cast_ofNat, zero_mul, add_zero, zero_add]
  ring
end MohP3.Gen
