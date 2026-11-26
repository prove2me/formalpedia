-- Prove2me | solution 1 for MohP3.arithRank_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:05:01.782395+00:00
-- url     : https://prove2.me/submissions/825bd4c0-3f1b-4418-ab2a-9455b3090ea5

module
public import Mathlib
public import Definitions.Def_MohP3_Ara

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MohP3
variable {A : Type*} [CommRing A]
namespace MohP3
theorem _root_.solution {I : Ideal A} (s : Finset A)
    (hs : (Ideal.span (s : Set A)).radical = I.radical) :
    arithRank I ≤ s.card :=
  iInf₂_le (f := fun (s : Finset A) _ => (s.card : ℕ∞)) s hs
end MohP3
