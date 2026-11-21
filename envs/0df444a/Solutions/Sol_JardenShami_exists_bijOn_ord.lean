-- Prove2me | solution 1 for JardenShami.exists_bijOn_ord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:43:44.213898+00:00
-- url     : https://prove2.me/submissions/330d3418-a350-40c5-a9dc-c6a08c1563be

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Theorems.Thm_JardenShami_Kappa_coe_mk
import Theorems.Thm_JardenShami_Kappa_mk_coe
attribute [local simp] JardenShami.Kappa.coe_mk
attribute [local simp] JardenShami.Kappa.mk_coe

set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}} {T : Type w} [PartialOrder T] [IsTree T]
omit [PartialOrder T] [IsTree T]
namespace JardenShami
theorem _root_.solution {L : Set T} {c : T} (hc : c ∈ L) :
    ∃ f : Ordinal.{w} → T, Set.BijOn f (Set.Iio (#L).ord) L ∧ f 0 = c := by
  classical
  have h0 : (0 : Ordinal.{w}) < (#L).ord := by
    rw [Cardinal.ord_pos, pos_iff_ne_zero, Cardinal.mk_ne_zero_iff]
    exact ⟨⟨c, hc⟩⟩
  obtain ⟨b⟩ : Nonempty (Set.Iio (#L).ord ≃ L) := by
    rw [← Cardinal.lift_mk_eq'.{w + 1, w}, Cardinal.mk_Iio_ordinal, Cardinal.card_ord]
    simp
  let b' : Set.Iio (#L).ord ≃ L := (Equiv.swap ⟨0, h0⟩ (b.symm ⟨c, hc⟩)).trans b
  have hb'0 : b' ⟨0, h0⟩ = ⟨c, hc⟩ := by simp [b']
  refine ⟨fun x => if h : x < (#L).ord then (b' ⟨x, h⟩ : T) else c, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x hx
    simp only [dif_pos (show x < (#L).ord from hx)]
    exact (b' ⟨x, hx⟩).2
  · intro x hx y hy hxy
    simp only [dif_pos (show x < (#L).ord from hx),
      dif_pos (show y < (#L).ord from hy)] at hxy
    exact congrArg Subtype.val (b'.injective (Subtype.ext hxy))
  · intro y hy
    have hx := (b'.symm ⟨y, hy⟩).2
    refine ⟨b'.symm ⟨y, hy⟩, hx, ?_⟩
    simp only [dif_pos (show (b'.symm ⟨y, hy⟩ : Ordinal.{w}) < (#L).ord from hx)]
    exact congrArg Subtype.val (b'.apply_symm_apply ⟨y, hy⟩)
  · simp only [dif_pos h0, hb'0]
end JardenShami
