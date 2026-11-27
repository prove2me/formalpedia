-- Prove2me | solution 1 for MohP3.HilbertBurch.xEquiv_X1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:11:31.265879+00:00
-- url     : https://prove2.me/submissions/9391c976-18ba-4c60-ac5d-f4eac358785d

module
public import Definitions.Def_MohP3_Generic
public import Mathlib
public import Definitions.Def_MohP3_HilbertBurch

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open MohP3 MohP3.HilbertBurch
open Matrix
open MvPolynomial
variable {K : Type*} [CommRing K]
namespace MohP3.HilbertBurch
theorem _root_.solution : xEquiv (X 1 : MvPolynomial (Fin 3) K) = Polynomial.C (X 0) :=
  finSuccEquiv_X_succ (j := 0)
end MohP3.HilbertBurch
