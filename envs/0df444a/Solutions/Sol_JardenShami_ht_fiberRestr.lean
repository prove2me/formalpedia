-- Prove2me | solution 1 for JardenShami.ht_fiberRestr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:45:55.039176+00:00
-- url     : https://prove2.me/submissions/ffbd52a8-2c1d-49bb-a0a6-5774af8a6807

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Theorems.Thm_JardenShami_fiberRestr_eq_fiberRestr
import Theorems.Thm_JardenShami_fiberRestr_ssubset_iff
import Theorems.Thm_JardenShami_Kappa_coe_lt_coe
import Theorems.Thm_JardenShami_Kappa_coe_mk
import Theorems.Thm_JardenShami_Kappa_mk_coe
attribute [local simp] JardenShami.Kappa.coe_mk
attribute [local simp] JardenShami.Kappa.mk_coe



set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}} {D : Type w}
namespace JardenShami
theorem _root_.solution (C : Coloring (Kappa κ) D) {δ β : Kappa κ} (h : β ≤ δ) :
    ht (⟨fiberRestr C δ β h, δ, β, h, rfl⟩ : treeOfColoring C) = (β : Ordinal.{w}) := by
  let g : treeOfColoring C := ⟨fiberRestr C δ β h, δ, β, h, rfl⟩
  have hk : ∀ a : Set.Iio (β : Ordinal.{w}), (a : Ordinal.{w}) < κ.ord :=
    fun a => a.2.trans (Kappa.coe_lt_ord β)
  have hkl : ∀ a : Set.Iio (β : Ordinal.{w}), Kappa.mk a (hk a) < β := fun a =>
    Kappa.coe_lt_coe.1 (by rw [Kappa.coe_mk]; exact a.2)
  let f : (fun x y : Set.Iio (β : Ordinal.{w}) => x < y) ↪r
      (fun x y : Set.Iio g => (x : treeOfColoring C) < y) :=
    RelEmbedding.ofMonotone
      (fun a => ⟨⟨fiberRestr C δ (Kappa.mk a (hk a)) ((hkl a).le.trans h), δ, _, _, rfl⟩,
        show fiberRestr C δ _ _ ⊂ fiberRestr C δ β h from
          (fiberRestr_ssubset_iff ((hkl a).le.trans h) h).2 ⟨hkl a, fun _ _ _ => rfl⟩⟩)
      (fun a b hab => show fiberRestr C δ _ _ ⊂ fiberRestr C δ _ _ from
        (fiberRestr_ssubset_iff ((hkl a).le.trans h) ((hkl b).le.trans h)).2
          ⟨by rw [← Kappa.coe_lt_coe, Kappa.coe_mk, Kappa.coe_mk]; exact hab,
            fun _ _ _ => rfl⟩)
  have e := RelIso.ofSurjective f (by
    rintro ⟨⟨_, δ', β', h', rfl⟩, hlt⟩
    have hss : fiberRestr C δ' β' h' ⊂ fiberRestr C δ β h := hlt
    obtain ⟨hββ, hag⟩ := (fiberRestr_ssubset_iff _ _).1 hss
    refine ⟨⟨β', Kappa.coe_lt_coe.2 hββ⟩, Subtype.ext (Subtype.ext ?_)⟩
    exact fiberRestr_eq_fiberRestr ((hkl _).le.trans h) h' (Kappa.mk_coe β')
      fun α hα₁ hα₂ => (hag α hα₂ (hα₂.trans hββ)).symm)
  have := e.ordinal_lift_type_eq
  unfold ht
  rw [Ordinal.type_lt_Iio, Ordinal.lift_lift] at this
  exact (Ordinal.lift_inj.1 this).symm
end JardenShami
