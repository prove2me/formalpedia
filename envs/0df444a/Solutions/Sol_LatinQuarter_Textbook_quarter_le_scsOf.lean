-- Prove2me | solution 1 for LatinQuarter.Textbook.quarter_le_scsOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:27:58.869644+00:00
-- url     : https://prove2.me/submissions/0f510d0c-b2d5-4977-935d-89dff8193513

module
public import Mathlib.SetTheory.Cardinal.Finite
public import Definitions.Def_LeanPool_LatinQuarter_Main
public import Definitions.Def_LeanPool_LatinQuarter_Parity
public import Definitions.Def_LeanPool_LatinQuarter_Textbook
public import Theorems.Thm_LatinQuarter_Textbook_definingSet_card
public import Theorems.Thm_LatinQuarter_Textbook_exists_criticalSet

set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter LatinQuarter.Textbook
namespace LatinQuarter.Textbook
theorem _root_.solution {n : ℕ} {L : Fin n → Fin n → Fin n} (hL : Latin L) :
    n * n / 4 ≤ scsOf L := by
  obtain ⟨T, hT⟩ := exists_criticalSet hL
  unfold scsOf
  exact le_csInf ⟨T.card, T, hT, rfl⟩ (by
    rintro m ⟨T', hT', rfl⟩
    exact definingSet_card hT'.1)
end LatinQuarter.Textbook
