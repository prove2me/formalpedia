-- Prove2me | solution 1 for JardenShami.nonempty_iso_iff_historyTree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:47:11.664898+00:00
-- url     : https://prove2.me/submissions/7afbe507-f028-4e6a-b5b7-1a69e0eead9a

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Theorems.Thm_JardenShami_histFun_orderIso
import Theorems.Thm_JardenShami_historyTree_iso_restrict_succPart
import Theorems.Thm_JardenShami_nonempty_iso_succPart_historyTree

set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {T : Type w} [PartialOrder T] [IsTree T]
namespace JardenShami
theorem _root_.solution {S : Type w} [PartialOrder S] [IsTree S]
    (hT : ∀ t : T, ¬ IsLeaf t) (hS : ∀ s : S, ¬ IsLeaf s) :
    Nonempty (T ≃o S) ↔ Nonempty (HistoryTree T ≃o HistoryTree S) := by
  constructor
  · rintro ⟨e⟩
    have hmapT : ∀ g : HistoryTree T, Prod.map id e '' g.1 ∈ HistoryTree S := by
      rintro ⟨_, t, rfl⟩
      exact ⟨e t, histFun_orderIso e t⟩
    have hmapS : ∀ g : HistoryTree S, Prod.map id e.symm '' g.1 ∈ HistoryTree T := by
      rintro ⟨_, t, rfl⟩
      exact ⟨e.symm t, histFun_orderIso e.symm t⟩
    have hinj : Function.Injective (Prod.map id e : Ordinal.{w} × T → Ordinal.{w} × S) :=
      Function.injective_id.prodMap e.injective
    refine ⟨
      { toFun := fun g => ⟨_, hmapT g⟩
        invFun := fun g => ⟨_, hmapS g⟩
        left_inv := ?_
        right_inv := ?_
        map_rel_iff' := ?_ }⟩
    · rintro ⟨g, hg⟩
      apply Subtype.ext
      change Prod.map id e.symm '' (Prod.map id e '' g) = g
      rw [Set.image_image]
      conv_rhs => rw [← Set.image_id g]
      congr 1
      funext x
      exact Prod.ext rfl (e.symm_apply_apply _)
    · rintro ⟨g, hg⟩
      apply Subtype.ext
      change Prod.map id e '' (Prod.map id e.symm '' g) = g
      rw [Set.image_image]
      conv_rhs => rw [← Set.image_id g]
      congr 1
      funext x
      exact Prod.ext rfl (e.apply_symm_apply _)
    · intro a b
      exact Set.image_subset_image_iff hinj
  · rintro ⟨g⟩
    obtain ⟨g', -⟩ := historyTree_iso_restrict_succPart g
    obtain ⟨eT⟩ := nonempty_iso_succPart_historyTree hT
    obtain ⟨eS⟩ := nonempty_iso_succPart_historyTree hS
    exact ⟨(eT.trans g').trans eS.symm⟩
end JardenShami
