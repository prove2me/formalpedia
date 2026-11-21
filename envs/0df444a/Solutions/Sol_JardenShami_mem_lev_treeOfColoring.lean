-- Prove2me | solution 1 for JardenShami.mem_lev_treeOfColoring
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:46:41.916016+00:00
-- url     : https://prove2.me/submissions/1a67aa73-90e0-4a17-a119-5bfab8ccad03

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Theorems.Thm_JardenShami_ht_fiberRestr

set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}} {D : Type w}
namespace JardenShami
theorem _root_.solution {C : Coloring (Kappa κ) D} {g : treeOfColoring C}
    {α : Ordinal.{w}} :
    g ∈ Lev (treeOfColoring C) α ↔
      ∃ (δ β : Kappa κ) (h : β ≤ δ), g.1 = fiberRestr C δ β h ∧ (β : Ordinal.{w}) = α := by
  obtain ⟨_, δ, β, h, rfl⟩ := g
  constructor
  · intro hg
    exact ⟨δ, β, h, rfl, (ht_fiberRestr C h).symm.trans hg⟩
  · rintro ⟨δ', β', h', he, rfl⟩
    change ht _ = _
    have : (⟨fiberRestr C δ β h, δ, β, h, rfl⟩ : treeOfColoring C) =
        ⟨fiberRestr C δ' β' h', δ', β', h', rfl⟩ := Subtype.ext he
    rw [this, ht_fiberRestr]
end JardenShami
