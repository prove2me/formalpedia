-- Prove2me | solution 1 for MohP3.Gen.wzD_wt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:25:18.304279+00:00
-- url     : https://prove2.me/submissions/e4988d0b-a3c1-4fac-8494-31ca0ef7115c

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
    10 + sig i ≤ 6 * (wzD i j t).2.1 + 8 * (wzD i j t).2.2.1 + 10 * (wzD i j t).2.2.2 + tau j := by
  fin_cases i <;> fin_cases j <;> fin_cases t <;> simp [wzD, sig, tau]
end MohP3.Gen
