-- Prove2me | solution 1 for LatinQuarter.Textbook.exists_criticalSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:24:42.749746+00:00
-- url     : https://prove2.me/submissions/30183cb5-a8cf-41f6-a14a-19c2ee46b848

module
public import Mathlib.SetTheory.Cardinal.Finite
public import Definitions.Def_LeanPool_LatinQuarter_Main
public import Definitions.Def_LeanPool_LatinQuarter_Parity
public import Definitions.Def_LeanPool_LatinQuarter_Textbook
public import Theorems.Thm_LatinQuarter_Textbook_exists_criticalSet_subset

set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter LatinQuarter.Textbook
namespace LatinQuarter.Textbook
theorem _root_.solution {n : ℕ} {L : Fin n → Fin n → Fin n} (hL : Latin L) :
    ∃ T, CriticalSet L T := by
  let T := (Finset.univ : Finset (Fin n × Fin n)).image
    (fun p => (p.1, p.2, L p.1 p.2))
  have hT : DefiningSet L T := by
    refine ⟨⟨hL, ?_⟩, ?_⟩
    · intro t ht
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp ht
      rfl
    · intro M hM
      funext r c
      exact hM.2 (r, c, L r c) (Finset.mem_image.mpr ⟨(r, c), Finset.mem_univ _, rfl⟩)
  obtain ⟨T', _, hT'⟩ := exists_criticalSet_subset T.card T rfl hT
  exact ⟨T', hT'⟩
end LatinQuarter.Textbook
