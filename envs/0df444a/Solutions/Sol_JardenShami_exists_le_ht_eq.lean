-- Prove2me | solution 1 for JardenShami.exists_le_ht_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:43:15.94325+00:00
-- url     : https://prove2.me/submissions/c8f9ead3-bf94-4e0b-8a28-4a6ec8d3faf8

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7

set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree
variable {T : Type w} [PartialOrder T] [IsTree T]
namespace JardenShami
theorem _root_.solution {t : T} {α : Ordinal.{w}} (h : α ≤ ht t) : ∃ s ≤ t, ht s = α := by
  rcases h.lt_or_eq with h | h
  · obtain ⟨s, hs, hsα⟩ := exists_lt_ht_eq h
    exact ⟨s, hs.le, hsα⟩
  · exact ⟨t, le_rfl, h.symm⟩
end JardenShami
