-- Prove2me | solution 1 for MohP3.HilbertBurch.range_phiMap_eq_ker_genMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:43:16.207464+00:00
-- url     : https://prove2.me/submissions/30879a07-994f-480e-9c78-1987e2fcb929

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
theorem _root_.solution : LinearMap.range (phiMap k) = LinearMap.ker (genMap k) :=
  (phi_exact_aux k).2
end MohP3.HilbertBurch
