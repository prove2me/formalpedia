-- Prove2me | solution 1 for MohP3.HilbertBurch.xEquiv_X2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:11:31.972574+00:00
-- url     : https://prove2.me/submissions/afa633ee-c827-42e2-a7ac-b34aea98fc41

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
theorem _root_.solution : xEquiv (X 2 : MvPolynomial (Fin 3) K) = Polynomial.C (X 1) :=
  finSuccEquiv_X_succ (j := 1)
end MohP3.HilbertBurch
