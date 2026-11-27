-- Prove2me | solution 1 for MohP3.HilbertBurch.phiMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:47:26.187346+00:00
-- url     : https://prove2.me/submissions/cd54d361-7d13-47ac-9577-deb10ce525c8

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
variable {A : Type*} [CommRing A]
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]
namespace MohP3.HilbertBurch
theorem _root_.solution (v : Fin 3 → S k) : phiMap k v = phi (X 0) (X 1) (X 2) *ᵥ v := rfl
end MohP3.HilbertBurch
