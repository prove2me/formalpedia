-- Prove2me | solution 1 for MohP3.HilbertBurch.phiMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:43:09.084484+00:00
-- url     : https://prove2.me/submissions/2ad3de4e-e7cc-4819-adeb-29f7082ba4fe

module
public import Definitions.Def_MohP3_Generic
public import Mathlib
public import Definitions.Def_MohP3_HilbertBurch
public import Theorems.Thm_MohP3_HilbertBurch_phi_exact_aux

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open MohP3 MohP3.HilbertBurch
open Matrix
open MvPolynomial
variable {A : Type*} [CommRing A]
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3.HilbertBurch
theorem _root_.solution : Function.Injective (phiMap k) := (phi_exact_aux k).1
end MohP3.HilbertBurch
