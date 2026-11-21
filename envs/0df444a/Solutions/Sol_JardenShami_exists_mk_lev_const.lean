-- Prove2me | solution 1 for JardenShami.exists_mk_lev_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:46:32.923836+00:00
-- url     : https://prove2.me/submissions/cd6b7943-0f04-409d-8e49-94658848bd68

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
import Theorems.Thm_JardenShami_mk_lev_mono
import Theorems.Thm_JardenShami_Kappa_coe_le_coe
import Theorems.Thm_JardenShami_Kappa_coe_lt_coe
import Theorems.Thm_JardenShami_Kappa_coe_mk
import Theorems.Thm_JardenShami_Kappa_exists_gt_of_card_lt
import Theorems.Thm_JardenShami_Kappa_mk_coe
import Theorems.Thm_JardenShami_Kappa_mk_eq
attribute [local simp] JardenShami.Kappa.coe_mk
attribute [local simp] JardenShami.Kappa.mk_coe



set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree
namespace JardenShami
theorem _root_.solution {κ lam : Cardinal.{w}} (hκ : κ.IsRegular) (hlam : lam < κ)
    {T : Type w} [PartialOrder T] [IsTree T] (hT : IsKappaTree κ T) (hwp : WellPruned T)
    (hlev : ∀ α : Ordinal.{w}, #(Lev T α) < lam) :
    ∃ α₀ < κ.ord, ∀ β : Ordinal.{w}, α₀ ≤ β → β < κ.ord → #(Lev T β) = #(Lev T α₀) := by
  classical
  let f : Kappa κ → Cardinal.{w} := fun α => #(Lev T (α : Ordinal.{w}))
  have hmono : Monotone f := fun a b hab =>
    mk_lev_mono hwp (Kappa.coe_le_coe.2 hab) (by rw [hT.1]; exact Kappa.coe_lt_ord b)
  have hfκ : ∀ α, (f α).ord < κ.ord := fun α =>
    Cardinal.ord_lt_ord.2 ((hlev _).trans hlam)
  suffices h : ∃ α₀ : Kappa κ, ∀ β, α₀ ≤ β → f β = f α₀ by
    obtain ⟨α₀, hα₀⟩ := h
    refine ⟨α₀, Kappa.coe_lt_ord α₀, fun β hβ hβκ => ?_⟩
    have := hα₀ (Kappa.mk β hβκ) (by rw [← Kappa.coe_le_coe, Kappa.coe_mk]; exact hβ)
    simpa [f] using this
  by_contra h
  push Not at h
  choose nxt hnxt hne using h
  have hgt : ∀ α, f α < f (nxt α) := fun α => lt_of_le_of_ne (hmono (hnxt α)) (hne α).symm
  -- code each size by an ordinal `< λ`
  let code : Kappa κ → Kappa κ := fun α => Kappa.mk (f α).ord (hfκ α)
  have hcode : ∀ a b, code a = code b → f a = f b := fun a b h => by
    have := congrArg (fun z : Kappa κ => (z : Ordinal.{w})) h
    simp only [code, Kappa.coe_mk] at this
    exact Cardinal.ord_injective this
  have hlamκ : lam.ord < κ.ord := Cardinal.ord_lt_ord.2 hlam
  have hV : #(Set.range code) < κ := by
    have hsub : Set.range code ⊆ Set.Iio (Kappa.mk lam.ord hlamκ) := by
      rintro _ ⟨α, rfl⟩
      rw [Set.mem_Iio, ← Kappa.coe_lt_coe, Kappa.coe_mk, Kappa.coe_mk]
      exact Cardinal.ord_lt_ord.2 (hlev _)
    refine (Cardinal.mk_le_mk_of_subset hsub).trans_lt ?_
    have := Cardinal.mk_Iio_lt (Kappa.mk lam.ord hlamκ)
      (by rw [Kappa.mk_eq, Ordinal.type_toType])
    rwa [Kappa.mk_eq] at this
  have : Nonempty (Kappa κ) :=
    ⟨Kappa.mk 0 (Cardinal.ord_pos.2 (Cardinal.aleph0_pos.trans_le hκ.aleph0_le))⟩
  let rep : Kappa κ → Kappa κ := Function.invFun code
  obtain ⟨z, hz⟩ := Kappa.exists_gt_of_card_lt hκ
    (Cardinal.mk_image_le.trans_lt hV : #((nxt ∘ rep) '' Set.range code) < κ)
  have hrep : code (rep (code z)) = code z := Function.invFun_eq ⟨z, rfl⟩
  have h1 : nxt (rep (code z)) < z := hz _ ⟨code z, ⟨z, rfl⟩, rfl⟩
  have h2 := hgt (rep (code z))
  rw [hcode _ _ hrep] at h2
  exact (hmono h1.le).not_gt h2
end JardenShami
