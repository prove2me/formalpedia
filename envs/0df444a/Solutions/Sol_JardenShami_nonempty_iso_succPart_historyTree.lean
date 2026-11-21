-- Prove2me | solution 1 for JardenShami.nonempty_iso_succPart_historyTree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:46:31.974086+00:00
-- url     : https://prove2.me/submissions/84bcf257-1c1e-447f-9710-6cf3d37b5ca4

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Theorems.Thm_JardenShami_histFun_eq_iff
import Theorems.Thm_JardenShami_mem_succPart_historyTree
import Theorems.Thm_JardenShami_Iio_succNode
import Theorems.Thm_JardenShami_ht_succNode

set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {T : Type w} [PartialOrder T] [IsTree T]
namespace JardenShami
theorem _root_.solution (hT : ∀ t : T, ¬ IsLeaf t) :
    Nonempty (T ≃o succPart (HistoryTree T)) := by
  classical
  have hmem : ∀ t : T, (⟨histFun (succNode (hT t)), _, rfl⟩ : HistoryTree T) ∈
      succPart (HistoryTree T) :=
    fun t => (mem_succPart_historyTree _).2
      ⟨succNode (hT t), ⟨ht t, ht_succNode (hT t)⟩, rfl⟩
  let h : T → succPart (HistoryTree T) := fun t => ⟨_, hmem t⟩
  have hle : ∀ a b, h a ≤ h b ↔ a ≤ b := by
    intro a b
    change histFun (succNode (hT a)) ⊆ histFun (succNode (hT b)) ↔ a ≤ b
    rw [histFun_subset_iff, Iio_succNode, Iio_succNode, Set.Iic_subset_Iic]
  refine ⟨RelIso.ofSurjective (OrderEmbedding.ofMapLEIff h hle) ?_⟩
  rintro ⟨⟨_, s, rfl⟩, hy⟩
  obtain ⟨t', ⟨β, hβ⟩, hst⟩ := (mem_succPart_historyTree _).1 hy
  rw [histFun_eq_iff] at hst
  have hsucc : ht s = Order.succ β := by
    rw [← hβ]
    exact le_antisymm (ht_le_ht_of_Iio_subset hst.le) (ht_le_ht_of_Iio_subset hst.ge)
  obtain ⟨p, hp, hpβ⟩ := exists_lt_ht_eq (hsucc ▸ Order.lt_succ_of_not_isMax (not_isMax β))
  have hIio : Set.Iio s = Set.Iic p := by
    ext x
    constructor
    · intro hx
      rcases lt_trichotomy_of_lt hx hp with h' | rfl | h'
      · exact h'.le
      · exact le_rfl
      · have := ht_lt_ht h'
        have := ht_lt_ht hx
        rw [hpβ] at *
        rw [hsucc] at this
        exact absurd (Order.lt_succ_iff.1 this) (not_le.2 ‹β < ht x›)
    · intro hx
      exact lt_of_le_of_lt hx hp
  refine ⟨p, Subtype.ext (Subtype.ext ?_)⟩
  change histFun (succNode (hT p)) = histFun s
  rw [histFun_eq_iff, Iio_succNode, hIio]
end JardenShami
