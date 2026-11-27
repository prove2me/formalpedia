-- Prove2me | solution 1 for MohP3.Gen.qzD_wt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:25:15.902834+00:00
-- url     : https://prove2.me/submissions/3115c038-d8fb-4c4b-90ca-cafe4a79bacb

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
theorem _root_.solution (i j : Fin 8) : 10 + sig i ≤ 8 * (qzD i j).2 + sig j := by
  fin_cases i <;> fin_cases j <;> simp [qzD, sig]
end MohP3.Gen
