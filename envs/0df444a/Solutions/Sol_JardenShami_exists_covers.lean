-- Prove2me | solution 1 for JardenShami.exists_covers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:46:00.538396+00:00
-- url     : https://prove2.me/submissions/f8298a3e-3b97-4fc0-9243-1d1ed823635e

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Theorems.Thm_JardenShami_Tree_ht_lt_height
import Theorems.Thm_JardenShami_Tree_lev_nonempty
import Theorems.Thm_JardenShami_Kappa_coe_le_coe
import Theorems.Thm_JardenShami_Kappa_coe_mk
import Theorems.Thm_JardenShami_Kappa_mk_coe
import Theorems.Thm_JardenShami_exists_bijOn_ord
attribute [local simp] JardenShami.Kappa.coe_mk
attribute [local simp] JardenShami.Kappa.mk_coe

set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}} {T : Type w} [PartialOrder T] [IsTree T]
namespace JardenShami
theorem _root_.solution (hκ : ℵ₀ ≤ κ) (hT : IsKappaTree κ T) (hwp : WellPruned T) :
    ∃ e : Enumeration κ T, e.Covers := by
  classical
  have hκ0 : (0 : Ordinal.{w}) < κ.ord := by
    rw [Cardinal.ord_pos]
    exact Cardinal.aleph0_pos.trans_le hκ
  obtain ⟨t₀, -⟩ := lev_nonempty (hT.1 ▸ hκ0 : (0 : Ordinal.{w}) < height T)
  have : Nonempty T := ⟨t₀⟩
  have hK : #(Kappa κ) = κ := by rw [Cardinal.mk_toType, Cardinal.card_ord]
  -- `|T| ≤ κ`
  have hcardT : #T ≤ κ := by
    have hU : (⋃ α : Kappa κ, Lev T (α : Ordinal.{w})) = Set.univ := by
      refine Set.eq_univ_of_forall fun t => Set.mem_iUnion.2 ?_
      refine ⟨Kappa.mk (ht t) (hT.1 ▸ ht_lt_height t), ?_⟩
      exact (Kappa.coe_mk _ _).symm
    rw [← Cardinal.mk_univ, ← hU]
    refine (Cardinal.mk_iUnion_le _).trans ?_
    rw [hK]
    calc κ * ⨆ α : Kappa κ, #(Lev T (α : Ordinal.{w})) ≤ κ * κ := by
          gcongr
          exact ciSup_le' fun α => (hT.2 _ (Kappa.coe_lt_ord α)).le
      _ = κ := Cardinal.mul_eq_self hκ
  -- a surjection `ρ : κ → T` and a bijection `E : κ ≃ κ × κ`
  obtain ⟨j⟩ : Nonempty (T ↪ Kappa κ) := by
    rw [← Cardinal.le_def, hK]
    exact hcardT
  let ρ : Kappa κ → T := Function.invFun j
  have hρ : Function.Surjective ρ := Function.invFun_surjective j.injective
  obtain ⟨E⟩ : Nonempty (Kappa κ ≃ Kappa κ × Kappa κ) := by
    rw [← Cardinal.eq, Cardinal.mk_prod, Cardinal.lift_id, hK, Cardinal.mul_eq_self hκ]
  let σ : Kappa κ → T := fun x => ρ (E x).2
  -- every node `t` is `σ δ` for some `δ > ht t`
  have hσ : ∀ t : T, ∃ δ : Kappa κ, ht t < (δ : Ordinal.{w}) ∧ σ δ = t := by
    intro t
    obtain ⟨k, hk⟩ := hρ t
    have htκ : ht t < κ.ord := hT.1 ▸ ht_lt_height t
    let x₀ : Kappa κ := Kappa.mk (ht t) htκ
    by_contra hc
    push Not at hc
    have hle : ∀ γ : Kappa κ, E.symm (γ, k) ≤ x₀ := by
      intro γ
      rw [← Kappa.coe_le_coe, Kappa.coe_mk]
      by_contra h'
      refine hc _ (lt_of_not_ge h') ?_
      simp [σ, hk]
    have hinj : Function.Injective fun γ : Kappa κ => (⟨E.symm (γ, k), hle γ⟩ : Set.Iic x₀) := by
      intro γ γ' h
      have := E.symm.injective (congrArg Subtype.val h)
      exact (Prod.mk.inj this).1
    have h1 := Cardinal.mk_le_of_injective hinj
    rw [hK, ← Set.Iio_insert] at h1
    have h2 : #(Set.Iio x₀) < κ := by
      have := Cardinal.mk_Iio_lt x₀ (by rw [hK, Ordinal.type_toType])
      rwa [hK] at this
    have h3 := (Cardinal.mk_insert_le (a := x₀) (s := Set.Iio x₀)).trans_lt
      (Cardinal.add_lt_of_lt hκ h2 (Cardinal.one_lt_aleph0.trans_le hκ))
    exact absurd (h1.trans_lt h3) (lt_irrefl κ)
  -- the nodes `t^0_δ`
  have hc : ∀ δ : Kappa κ, ∃ y ∈ Lev T (δ : Ordinal.{w}),
      ht (σ δ) < (δ : Ordinal.{w}) → σ δ < y := by
    intro δ
    have hδ : (δ : Ordinal.{w}) < height T := by rw [hT.1]; exact Kappa.coe_lt_ord δ
    by_cases h : ht (σ δ) < (δ : Ordinal.{w})
    · obtain ⟨y, hy, hlt⟩ := hwp.2 (σ δ) δ h hδ
      exact ⟨y, hy, fun _ => hlt⟩
    · obtain ⟨y, hy⟩ := lev_nonempty hδ
      exact ⟨y, hy, fun h' => absurd h' h⟩
  choose c hcL hcσ using hc
  -- the enumeration
  have hf : ∀ α : Ordinal.{w}, ∃ f : Ordinal.{w} → T, ∀ hα : α < κ.ord,
      Set.BijOn f (Set.Iio (#(Lev T α)).ord) (Lev T α) ∧ f 0 = c (Kappa.mk α hα) := by
    intro α
    by_cases hα : α < κ.ord
    · have hmem : c (Kappa.mk α hα) ∈ Lev T α := by
        simpa using hcL (Kappa.mk α hα)
      obtain ⟨f, hf, hf0⟩ := exists_bijOn_ord hmem
      exact ⟨f, fun _ => ⟨hf, hf0⟩⟩
    · exact ⟨fun _ => t₀, fun h => absurd h hα⟩
  choose tf htf using hf
  refine ⟨⟨tf, fun α hα => (htf α hα).1⟩, fun t => ?_⟩
  obtain ⟨δ, hδ, hσδ⟩ := hσ t
  refine ⟨δ, Kappa.coe_lt_ord δ, ?_⟩
  change t < tf δ 0
  rw [(htf δ (Kappa.coe_lt_ord δ)).2, Kappa.mk_coe, ← hσδ]
  exact hcσ δ (by rw [hσδ]; exact hδ)
end JardenShami
