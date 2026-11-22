-- Prove2me | solution 1 for LatinQuarter.Textbook.completes_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:24:06.510443+00:00
-- url     : https://prove2.me/submissions/b6acb7f2-b570-4ca7-8656-1e5008a28de8

module
public import Mathlib.SetTheory.Cardinal.Finite
public import Definitions.Def_LeanPool_LatinQuarter_Main
public import Definitions.Def_LeanPool_LatinQuarter_Parity
public import Definitions.Def_LeanPool_LatinQuarter_Textbook

set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter LatinQuarter.Textbook
namespace LatinQuarter.Textbook
theorem _root_.solution {n : ℕ} {T : Finset (Fin n × Fin n × Fin n)}
    {L : Fin n → Fin n → Fin n} (hL : Completes T L) (M : Fin n → Fin n → Fin n) :
    Completes T M ↔ IsLatin M ∧ Agrees (T.image fun t => (t.1, t.2.1)) L M := by
  constructor
  · rintro ⟨hM, hMT⟩
    refine ⟨(latin_iff M).mp hM, ?_⟩
    intro p hp
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
    exact (hMT t ht).trans (hL.2 t ht).symm
  · rintro ⟨hM, hMa⟩
    refine ⟨(latin_iff M).mpr hM, ?_⟩
    intro t ht
    exact (hMa _ (Finset.mem_image.mpr ⟨t, ht, rfl⟩)).trans (hL.2 t ht)
end LatinQuarter.Textbook
