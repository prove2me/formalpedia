-- Prove2me | solution 1 for MohP3.Gen.key_xA_0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:22:22.933944+00:00
-- url     : https://prove2.me/submissions/8b372efa-b68d-42b9-869b-6a8bfc56b62d

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
    (18 : A) * (x * hh x y z 0) =
      (∑ j, qxA y 0 j * hh x y z j) + ∑ j, wxA x y z 0 j * ff x y z j := by
  simp only [hh, ff, qxA, wxA, qxD, wxD, f1, f2, f3, f4, Fin.sum_univ_eight,
    Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Int.cast_zero, Int.cast_ofNat, zero_mul, add_zero, zero_add]
  ring
end MohP3.Gen
