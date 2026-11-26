-- Prove2me | solution 1 for MohP3.mem_minimalPrimes_of_radical_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:03:58.675025+00:00
-- url     : https://prove2.me/submissions/1ebc1024-1b96-4ebc-bf04-b5a70335eaad

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
theorem _root_.solution {I p : Ideal A} (hp : p.IsPrime)
    (h : I.radical = p) : p ∈ I.minimalPrimes := by
  refine ⟨⟨hp, h ▸ Ideal.le_radical⟩, ?_⟩
  rintro q ⟨hq, hIq⟩ _
  exact h ▸ hq.radical_le_iff.mpr hIq
end MohP3
