-- Prove2me | solution 1 for JardenShami.histFun_orderIso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:44:38.975458+00:00
-- url     : https://prove2.me/submissions/7e8c87dd-14d4-470a-a51a-bba3eeac9e06

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Theorems.Thm_JardenShami_ht_orderIso

set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {T : Type w} [PartialOrder T] [IsTree T]
namespace JardenShami
theorem _root_.solution {S : Type w} [PartialOrder S] [IsTree S] (e : T ≃o S) (t : T) :
    histFun (e t) = Prod.map id e '' histFun t := by
  ext ⟨α, q⟩
  constructor
  · rintro ⟨hq, hα⟩
    refine ⟨(α, e.symm q), ⟨?_, ?_⟩, by simp⟩
    · simpa using e.symm.lt_iff_lt.2 hq
    · rw [← hα, ← ht_orderIso e (e.symm q), e.apply_symm_apply]
  · rintro ⟨⟨β, p⟩, ⟨hp, hβ⟩, h⟩
    simp only [Prod.map, id, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨e.lt_iff_lt.2 hp, by rw [ht_orderIso e p, hβ]⟩
end JardenShami
