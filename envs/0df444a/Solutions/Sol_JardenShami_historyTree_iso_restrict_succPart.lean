-- Prove2me | solution 1 for JardenShami.historyTree_iso_restrict_succPart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:44:39.54425+00:00
-- url     : https://prove2.me/submissions/b5c6fd6b-cdca-4954-80dc-c47cdfdbc31c

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
theorem _root_.solution {S : Type w} [PartialOrder S] [IsTree S]
    (g : HistoryTree T ≃o HistoryTree S) :
    ∃ g' : succPart (HistoryTree T) ≃o succPart (HistoryTree S),
      ∀ x : succPart (HistoryTree T), (g' x : HistoryTree S) = g x := by
  have hg : ∀ x, x ∈ succPart (HistoryTree T) ↔ g x ∈ succPart (HistoryTree S) := by
    intro x
    change (∃ β, ht x = Order.succ β) ↔ ∃ β, ht (g x) = Order.succ β
    rw [ht_orderIso]
  exact ⟨{ toEquiv := g.toEquiv.subtypeEquiv hg, map_rel_iff' := g.le_iff_le }, fun _ => rfl⟩
end JardenShami
