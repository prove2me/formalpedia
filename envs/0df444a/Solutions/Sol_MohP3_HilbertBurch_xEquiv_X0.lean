-- Prove2me | solution 1 for MohP3.HilbertBurch.xEquiv_X0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:37:55.897795+00:00
-- url     : https://prove2.me/submissions/43463923-3ce9-4c7d-9ef8-25477c39dd03

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
theorem _root_.solution : xEquiv (X 0 : MvPolynomial (Fin 3) K) = Polynomial.X := finSuccEquiv_X_zero
end MohP3.HilbertBurch
