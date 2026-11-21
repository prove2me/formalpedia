-- Prove2me | solution 1 for JardenShami.mk_lev_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:45:42.875634+00:00
-- url     : https://prove2.me/submissions/a1f233f7-5095-4147-82d2-f90be997c1f1

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
import Theorems.Thm_JardenShami_exists_le_ht_eq
import Theorems.Thm_JardenShami_Tree_eq_of_le_of_le_of_ht_eq


set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree
namespace JardenShami
theorem _root_.solution {T : Type w} [PartialOrder T] [IsTree T] (hwp : WellPruned T)
    {α β : Ordinal.{w}} (hαβ : α ≤ β) (hβ : β < height T) : #(Lev T α) ≤ #(Lev T β) := by
  classical
  rcases hαβ.lt_or_eq with hlt | rfl
  · have hr : ∀ y : Lev T β, ∃ x : Lev T α, (x : T) ≤ y := by
      intro y
      obtain ⟨x, hxy, hx⟩ := exists_le_ht_eq (show α ≤ ht (y : T) by rw [y.2]; exact hlt.le)
      exact ⟨⟨x, hx⟩, hxy⟩
    choose r hr using hr
    refine Cardinal.mk_le_of_surjective (f := r) fun x => ?_
    obtain ⟨y, hy, hxy⟩ := hwp.2 x β (by rw [x.2]; exact hlt) hβ
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    exact eq_of_le_of_le_of_ht_eq (hr ⟨y, hy⟩) hxy.le ((r ⟨y, hy⟩).2.trans x.2.symm)
  · exact le_rfl
end JardenShami
