-- Prove2me | solution 1 for MohP3.height_le_arithRank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:05:23.041488+00:00
-- url     : https://prove2.me/submissions/5cc77d57-b4e9-4357-b56d-31d9236747bc

module
public import Mathlib
public import Definitions.Def_MohP3_Ara
public import Theorems.Thm_MohP3_mem_minimalPrimes_of_radical_eq

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MohP3
variable {A : Type*} [CommRing A]
namespace MohP3
theorem _root_.solution [IsNoetherianRing A] (p : Ideal A) (hp : p.IsPrime) :
    p.height ≤ arithRank p := by
  refine le_iInf₂ fun s hs => ?_
  refine Ideal.height_le_card_of_mem_minimalPrimes_span_finset
    (mem_minimalPrimes_of_radical_eq hp ?_)
  rw [hs, hp.radical]
end MohP3
