-- Prove2me | solution 1 for MohP3.Gen.wxD_wt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:25:17.803802+00:00
-- url     : https://prove2.me/submissions/e2c2c332-5763-4954-8735-9d43be856671

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
theorem _root_.solution (i : Fin 8) (j : Fin 4) (t : Fin 4) :
    6 + sig i ≤ 6 * (wxD i j t).2.1 + 8 * (wxD i j t).2.2.1 + 10 * (wxD i j t).2.2.2 + tau j := by
  fin_cases i <;> fin_cases j <;> fin_cases t <;> simp [wxD, sig, tau]
end MohP3.Gen
