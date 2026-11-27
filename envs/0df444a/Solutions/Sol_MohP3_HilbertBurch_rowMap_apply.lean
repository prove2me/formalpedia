-- Prove2me | solution 1 for MohP3.HilbertBurch.rowMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:10:32.87097+00:00
-- url     : https://prove2.me/submissions/034a801c-e40b-4dea-b971-0e2369749327

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
variable {S : Type*} [CommRing S]
namespace MohP3.HilbertBurch
theorem _root_.solution (f : Fin 4 → S) (a : Fin 4 → S) : rowMap f a = a ⬝ᵥ f := rfl
end MohP3.HilbertBurch
