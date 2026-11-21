-- Prove2me | solution 1 for JardenShami.ht_binRestr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:45:24.757978+00:00
-- url     : https://prove2.me/submissions/8844e42c-1d92-45f5-8287-843210fa598d

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
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
variable {ν : Cardinal.{w}}
namespace JardenShami
theorem _root_.solution (f : Kappa ν → Fin 2) (β : Kappa ν) :
    ht (⟨binRestr f β, f, β, rfl⟩ : binTree ν) = (β : Ordinal.{w}) := by
  let g : binTree ν := ⟨binRestr f β, f, β, rfl⟩
  have hk : ∀ a : Set.Iio (β : Ordinal.{w}), (a : Ordinal.{w}) < ν.ord :=
    fun a => a.2.trans (Kappa.coe_lt_ord β)
  have hkl : ∀ a : Set.Iio (β : Ordinal.{w}), Kappa.mk a (hk a) < β := fun a =>
    Kappa.coe_lt_coe.1 (by rw [Kappa.coe_mk]; exact a.2)
  have hss : ∀ {a b : Kappa ν}, a < b → binRestr f a ⊂ binRestr f b := fun {a b} h =>
    ⟨binRestr_subset_iff.2 ⟨h.le, fun _ _ => rfl⟩,
      fun h' => h.not_ge (binRestr_subset_iff.1 h').1⟩
  let F : (fun x y : Set.Iio (β : Ordinal.{w}) => x < y) ↪r
      (fun x y : Set.Iio g => (x : binTree ν) < y) :=
    RelEmbedding.ofMonotone
      (fun a => ⟨⟨binRestr f (Kappa.mk a (hk a)), f, _, rfl⟩,
        show binRestr f _ ⊂ binRestr f β from hss (hkl a)⟩)
      (fun a b hab => show binRestr f _ ⊂ binRestr f _ from
        hss (by rw [← Kappa.coe_lt_coe, Kappa.coe_mk, Kappa.coe_mk]; exact hab))
  have e := RelIso.ofSurjective F (by
    rintro ⟨⟨_, f', β', rfl⟩, hlt⟩
    have hs : binRestr f' β' ⊂ binRestr f β := hlt
    obtain ⟨hββ, hag⟩ := binRestr_subset_iff.1 hs.1
    have hββ' : β' < β := hββ.lt_of_ne fun he =>
      hs.2 (binRestr_eq_iff.2 ⟨he, hag⟩).symm.le
    refine ⟨⟨β', Kappa.coe_lt_coe.2 hββ'⟩, Subtype.ext (Subtype.ext ?_)⟩
    exact binRestr_eq_iff.2 ⟨Kappa.mk_coe β', fun α hα => (hag α (by
      rwa [Kappa.mk_coe] at hα)).symm⟩)
  have := e.ordinal_lift_type_eq
  unfold ht
  rw [Ordinal.type_lt_Iio, Ordinal.lift_lift] at this
  exact (Ordinal.lift_inj.1 this).symm
end JardenShami
