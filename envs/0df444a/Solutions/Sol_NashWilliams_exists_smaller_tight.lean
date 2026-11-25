-- Prove2me | solution 1 for NashWilliams.exists_smaller_tight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:22:59.504717+00:00
-- url     : https://prove2.me/submissions/37155195-4ac2-4098-96b0-8b503d5b4a7d

module
public import Definitions.Def_NashWilliamsLib_Basic
public import Definitions.Def_NashWilliamsLib_Mader
public import Theorems.Thm_NashWilliams_cutF_inter_add_union
public import Theorems.Thm_NashWilliams_cutF_sdiff_add_sdiff


set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]
omit [DecidableEq ι]
namespace NashWilliams
theorem _root_.solution {K : ℕ} {T : Finset V} {ends : ι → V × V} {F : Finset ι}
    (hreq : Req K T ends F) {X Y : Finset V} (hX : Tight K T ends F X) (hY : Tight K T ends F Y)
    {a b : V} (haX : a ∈ X) (hbX : b ∈ X) (haY : a ∈ Y) (hbY : b ∉ Y) :
    ∃ Z, Tight K T ends F Z ∧ Z.card < X.card := by
  obtain ⟨hXT, hXne, hXT', hXc⟩ := hX
  obtain ⟨hYT, hYne, hYT', hYc⟩ := hY
  by_cases hU : X ∪ Y = T
  · have hpos := cutF_sdiff_add_sdiff ends F X Y
    have hYX : K ≤ cutF ends F (Y \ X) := by
      refine hreq _ (sdiff_subset.trans hYT) ?_ ?_
      · obtain ⟨t, htT, htX⟩ : ∃ t ∈ T, t ∉ X := by
          by_contra! h
          exact hXT' (Subset.antisymm hXT h)
        refine ⟨t, mem_sdiff.2 ⟨?_, htX⟩⟩
        rw [← hU] at htT
        simpa [htX] using htT
      · intro h
        have : a ∈ Y \ X := h ▸ hXT haX
        simp [haX] at this
    have hXY : K ≤ cutF ends F (X \ Y) := by
      refine hreq _ (sdiff_subset.trans hXT) ⟨b, by simp [hbX, hbY]⟩ ?_
      intro h
      have : a ∈ X \ Y := h ▸ hXT haX
      simp [haY] at this
    refine ⟨X \ Y, ⟨sdiff_subset.trans hXT, ⟨b, by simp [hbX, hbY]⟩, ?_, by omega⟩, ?_⟩
    · intro h
      have : a ∈ X \ Y := h ▸ hXT haX
      simp [haY] at this
    · exact card_lt_card ⟨sdiff_subset, fun h => by simpa [haY] using h haX⟩
  · have hsub := cutF_inter_add_union ends F X Y
    have hU' : K ≤ cutF ends F (X ∪ Y) :=
      hreq _ (union_subset hXT hYT) ⟨a, by simp [haX]⟩ hU
    have hI : K ≤ cutF ends F (X ∩ Y) := by
      refine hreq _ (inter_subset_left.trans hXT) ⟨a, by simp [haX, haY]⟩ ?_
      intro h
      have : b ∈ X ∩ Y := h ▸ hXT hbX
      simp [hbY] at this
    refine ⟨X ∩ Y, ⟨inter_subset_left.trans hXT, ⟨a, by simp [haX, haY]⟩, ?_, by omega⟩, ?_⟩
    · intro h
      have : b ∈ X ∩ Y := h ▸ hXT hbX
      simp [hbY] at this
    · exact card_lt_card ⟨inter_subset_left, fun h => by simpa [hbY] using h hbX⟩
end NashWilliams
