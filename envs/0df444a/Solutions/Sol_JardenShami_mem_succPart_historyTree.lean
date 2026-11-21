-- Prove2me | solution 1 for JardenShami.mem_succPart_historyTree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:45:54.481472+00:00
-- url     : https://prove2.me/submissions/8badfa15-78bf-46ac-bc12-43199569a2ce

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Theorems.Thm_JardenShami_ht_histFun

set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {T : Type w} [PartialOrder T] [IsTree T]
namespace JardenShami
theorem _root_.solution (g : HistoryTree T) :
    g ∈ succPart (HistoryTree T) ↔ ∃ t ∈ succPart T, g.1 = histFun t := by
  obtain ⟨_, s, rfl⟩ := g
  have hls : ∀ a : Ordinal.{w}, Ordinal.lift.{w + 1} (Order.succ a) =
      Order.succ (Ordinal.lift.{w + 1} a) := by
    intro a
    rw [Order.succ_eq_add_one, Order.succ_eq_add_one, Ordinal.lift_add_one]
  have key : (∃ β, Ordinal.lift.{w + 1} (ht s) = Order.succ β) ↔ ∃ β, ht s = Order.succ β := by
    constructor
    · rintro ⟨β, hβ⟩
      obtain ⟨β', rfl⟩ := Ordinal.mem_range_lift_of_le (hβ ▸ (Order.le_succ β))
      exact ⟨β', Ordinal.lift_inj.1 (by rw [hβ, hls])⟩
    · rintro ⟨β, hβ⟩
      exact ⟨Ordinal.lift.{w + 1} β, by rw [hβ, hls]⟩
  constructor
  · rintro ⟨β, hβ⟩
    rw [ht_histFun] at hβ
    exact ⟨s, key.1 ⟨β, hβ⟩, rfl⟩
  · rintro ⟨t, ⟨β, hβ⟩, hst⟩
    have hg : (⟨histFun s, s, rfl⟩ : HistoryTree T) = ⟨histFun t, t, rfl⟩ := Subtype.ext hst
    change ∃ β, _ = _
    rw [hg, ht_histFun]
    exact ⟨Ordinal.lift.{w + 1} β, by rw [hβ, hls]⟩
end JardenShami
