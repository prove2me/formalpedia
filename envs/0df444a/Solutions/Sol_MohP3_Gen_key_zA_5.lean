-- Prove2me | solution 1 for MohP3.Gen.key_zA_5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:24:18.053822+00:00
-- url     : https://prove2.me/submissions/1c7dadad-7d6d-4dff-93aa-2a7f8bb5d536

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
    (18 : A) * (z * hh x y z 5) =
      (∑ j, qzA y 5 j * hh x y z j) + ∑ j, wzA x y z 5 j * ff x y z j := by
  simp only [hh, ff, qzA, wzA, qzD, wzD, f1, f2, f3, f4, Fin.sum_univ_eight,
    Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Int.cast_zero, Int.cast_ofNat, Int.cast_neg, zero_mul, add_zero, zero_add]
  ring
end MohP3.Gen
