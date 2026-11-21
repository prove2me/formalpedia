-- Prove2me | solution 1 for JardenShami.exists_nonsplitting
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:47:09.364351+00:00
-- url     : https://prove2.me/submissions/4b82d42c-bb7e-439d-a338-393898db1f91

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
import Theorems.Thm_JardenShami_exists_le_ht_eq
import Theorems.Thm_JardenShami_le_mk_lev_of_splitting
import Theorems.Thm_JardenShami_exists_mk_lev_const
import Theorems.Thm_JardenShami_exists_closed_level
import Theorems.Thm_JardenShami_Tree_eq_of_le_of_le_of_ht_eq
import Theorems.Thm_JardenShami_Tree_ht_lt_height
import Theorems.Thm_JardenShami_Tree_lev_nonempty


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
    ∃ a : T, ∀ b c : T, a < b → a < c → ht b = ht c → b = c := by
  classical
  obtain ⟨α₀, hα₀, hconst⟩ := exists_mk_lev_const hκ hlam hT hwp hlev
  by_contra hns
  push Not at hns
  have hα₀h : α₀ < height T := by rw [hT.1]; exact hα₀
  obtain ⟨a₀, ha₀⟩ := lev_nonempty hα₀h
  rcases lt_or_ge (#(Lev T α₀)) ℵ₀ with hfin | hinf
  · -- finite constant size: the restriction map is a bijection, so `a₀` cannot split
    obtain ⟨b, c, hab, hac, hbc, hne⟩ := hns a₀
    set β := ht b with hβdef
    have hβ : β < κ.ord := hT.1 ▸ ht_lt_height b
    have hα₀β : α₀ < β := by rw [← show ht a₀ = α₀ from ha₀]; exact ht_lt_ht hab
    have hr : ∀ y : Lev T β, ∃ x : Lev T α₀, (x : T) ≤ y := by
      intro y
      obtain ⟨x, hxy, hx⟩ := exists_le_ht_eq (show α₀ ≤ ht (y : T) by rw [y.2]; exact hα₀β.le)
      exact ⟨⟨x, hx⟩, hxy⟩
    choose r hr using hr
    have hsurj : Function.Surjective r := by
      intro x
      obtain ⟨y, hy, hxy⟩ := hwp.2 x β (by rw [x.2]; exact hα₀β) (by rw [hT.1]; exact hβ)
      refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
      exact eq_of_le_of_le_of_ht_eq (hr ⟨y, hy⟩) hxy.le ((r ⟨y, hy⟩).2.trans x.2.symm)
    have hfinβ : Finite (Lev T β) := Cardinal.lt_aleph0_iff_finite.1
      ((hconst β hα₀β.le hβ).trans_lt hfin)
    obtain ⟨e⟩ : Nonempty (Lev T β ≃ Lev T α₀) := Cardinal.eq.1 (hconst β hα₀β.le hβ)
    have hinj := (Finite.injective_iff_surjective_of_equiv e).2 hsurj
    have hrb : r ⟨b, rfl⟩ = ⟨a₀, ha₀⟩ := Subtype.ext (eq_of_le_of_le_of_ht_eq (hr ⟨b, rfl⟩)
      hab.le ((r ⟨b, rfl⟩).2.trans ha₀.symm))
    have hrc : r ⟨c, hbc.symm⟩ = ⟨a₀, ha₀⟩ := Subtype.ext (eq_of_le_of_le_of_ht_eq
      (hr ⟨c, hbc.symm⟩) hac.le ((r ⟨c, hbc.symm⟩).2.trans ha₀.symm))
    exact hne (congrArg Subtype.val (hinj (hrb.trans hrc.symm)))
  · -- infinite constant size `n`: a level of size `≥ n⁺` contradicts `|Lev| = n`
    set n := #(Lev T α₀)
    have hρ : (Order.succ n).IsRegular := Cardinal.isRegular_succ hinf
    have hρκ : Order.succ n < κ := (Order.succ_le_of_lt (hlev α₀)).trans_lt hlam
    -- for each level `q`, the height `σ q` of a splitting above a node of `Lev_q`
    have hsp : ∀ q : Ordinal.{w}, ∃ s : Ordinal.{w}, q < κ.ord → s < κ.ord ∧
        ∃ a b c : T, ht a = q ∧ q < ht b ∧ ht b = s ∧ ht c = ht b ∧ a < b ∧ a < c ∧ b ≠ c := by
      intro q
      by_cases hq : q < κ.ord
      · obtain ⟨a, ha⟩ := lev_nonempty (show q < height T by rw [hT.1]; exact hq)
        obtain ⟨b, c, hab, hac, hbc, hne⟩ := hns a
        refine ⟨ht b, fun _ => ⟨hT.1 ▸ ht_lt_height b, a, b, c, ha, ?_, rfl, hbc.symm, hab,
          hac, hne⟩⟩
        rw [← show ht a = q from ha]
        exact ht_lt_ht hab
      · exact ⟨0, fun h => absurd h hq⟩
    choose σ hσ using hsp
    obtain ⟨α, hα₀α, hακ, hclosed, hbd⟩ := exists_closed_level hκ hρ hρκ hα₀ σ
      (fun q hq => (hσ q hq).1)
    have hle := le_mk_lev_of_splitting (T := T) (ρ := Order.succ n) (α := α) (α₀ := α₀)
      (fun x hx => hwp.2 x α hx (by rw [hT.1]; exact hακ)) hbd hα₀α
      (fun q _ hq => by
        obtain ⟨-, a, b, c, ha, hqb, hb, hcb, hab, hac, hne⟩ := hσ q (hq.trans hακ)
        exact ⟨a, b, c, ha, hqb, hb ▸ hclosed q hq, hcb, hab, hac, hne⟩)
    rw [hconst α hα₀α.le hακ] at hle
    exact (Order.lt_succ_of_not_isMax (not_isMax n)).not_ge hle
end JardenShami
