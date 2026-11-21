-- Prove2me | solution 1 for JardenShami.card_lev_treeOfColoring_le_of_aleph0_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:47:11.15602+00:00
-- url     : https://prove2.me/submissions/619bf954-6310-4fba-bf94-e3ed12ccafb9

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Theorems.Thm_JardenShami_Kappa_mk_eq
import Theorems.Thm_JardenShami_IsLocallyAdditive_color_eq_of_le
import Theorems.Thm_JardenShami_Coloring_color_congr
import Theorems.Thm_JardenShami_fiberRestr_eq_fiberRestr
import Theorems.Thm_JardenShami_mem_lev_treeOfColoring
import Theorems.Thm_JardenShami_Kappa_coe_inj
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
namespace JardenShami
theorem _root_.solution (κ μ : Cardinal.{w}) (hκ0 : ℵ₀ ≤ κ)
    (C : Coloring (Kappa κ) (Kappa μ)) (hC : IsLocallyAdditive C) :
    ∀ β : Ordinal.{w}, #(Lev (treeOfColoring C) β) ≤ μ := by
  classical
  intro β
  have hKμ : #(Kappa μ) = μ := Kappa.mk_eq μ
  -- `[κ]^2` is nonempty, hence there is at least one color
  have h1 : (1 : Ordinal.{w}) < κ.ord := by
    rw [Cardinal.lt_ord, Ordinal.card_one]
    exact Cardinal.one_lt_aleph0.trans_le hκ0
  have h0 : (0 : Ordinal.{w}) < κ.ord := zero_lt_one.trans h1
  have h01 : Kappa.mk 0 h0 < Kappa.mk 1 h1 := by
    rw [← Kappa.coe_lt_coe, Kappa.coe_mk, Kappa.coe_mk]
    exact zero_lt_one
  have hμ0 : μ ≠ 0 := by
    rw [← hKμ]
    exact Cardinal.mk_ne_zero_iff.2 ⟨C.color _ _ h01⟩
  by_cases hβ : β < κ.ord
  swap
  · have : Lev (treeOfColoring C) β = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun g hg => ?_
      obtain ⟨δ, β', h, -, hβ'⟩ := mem_lev_treeOfColoring.1 hg
      exact hβ (hβ' ▸ Kappa.coe_lt_ord β')
    rw [this]
    simp
  set b : Kappa κ := Kappa.mk β hβ with hb
  -- every node of level `β` is `C(·,δ) ↾ b` for some `δ ≥ b`
  have hnode : ∀ g ∈ Lev (treeOfColoring C) β,
      ∃ δ, b ≤ δ ∧ ∀ h : b ≤ δ, g.1 = fiberRestr C δ b h := by
    intro g hg
    obtain ⟨δ, β', h, hg, hβ'⟩ := mem_lev_treeOfColoring.1 hg
    have : β' = b := Kappa.coe_inj.1 (by rw [hβ', hb, Kappa.coe_mk])
    subst this
    exact ⟨δ, h, fun _ => hg⟩
  have : Nonempty (Kappa κ) := ⟨b⟩
  choose! dl hdl hgdl using hnode
  -- two nodes of level `β` whose colors agree below `b` are equal
  have heq : ∀ (g : treeOfColoring C) (hg : g ∈ Lev (treeOfColoring C) β)
      (g' : treeOfColoring C) (hg' : g' ∈ Lev (treeOfColoring C) β),
      (∀ (α : Kappa κ) (hα : α < b), C.color α (dl g) (hα.trans_le (hdl g hg)) =
        C.color α (dl g') (hα.trans_le (hdl g' hg'))) → g = g' := by
    intro g hg g' hg' hc
    refine Subtype.ext ?_
    rw [hgdl g hg (hdl g hg), hgdl g' hg' (hdl g' hg')]
    exact fiberRestr_eq_fiberRestr _ _ rfl fun α hα _ => hc α hα
  rcases le_or_gt ℵ₀ μ with hinf | hfin
  · -- `μ` infinite: inject the level into `μ + 1`
    let φ : Lev (treeOfColoring C) β → Option (Kappa μ) := fun g =>
      if h : b < dl g then some (C.color b (dl g) h) else none
    have hφ : Function.Injective φ := by
      rintro ⟨g, hg⟩ ⟨g', hg'⟩ e
      refine Subtype.ext (heq g hg g' hg' fun α hα => ?_)
      by_cases h : b < dl g <;> by_cases h' : b < dl g'
      · simp only [φ, dif_pos h,
          dif_pos h', Option.some.injEq] at e
        exact hC.color_eq_of_le h h' e hα.le
      · simp [φ, h, h'] at e
      · simp [φ, h, h'] at e
      · have e1 : dl g = b := le_antisymm (not_lt.1 h) (hdl g hg)
        have e2 : dl g' = b := le_antisymm (not_lt.1 h') (hdl g' hg')
        exact C.color_congr rfl (e1.trans e2.symm) _ _
    calc #(Lev (treeOfColoring C) β) ≤ #(Option (Kappa μ)) := Cardinal.mk_le_of_injective hφ
      _ = μ + 1 := by rw [Cardinal.mk_option, hKμ]
      _ = μ := Cardinal.add_one_of_aleph0_le hinf
  · -- `μ = n` finite: `n + 1` distinct nodes give `n + 1` distinct colors `C(a,·)`
    obtain ⟨n, rfl⟩ := Cardinal.lt_aleph0.1 hfin
    by_contra hc
    have hn1 : ((n + 1 : ℕ) : Cardinal.{w}) ≤ #(Lev (treeOfColoring C) β) := by
      rw [Nat.cast_succ, ← Cardinal.succ_natCast]
      exact Order.succ_le_of_lt (lt_of_not_ge hc)
    obtain ⟨p, hpL, hpc⟩ := Cardinal.le_mk_iff_exists_subset.1 hn1
    have hpfin : p.Finite := Cardinal.lt_aleph0_iff_set_finite.1 (hpc ▸ Cardinal.natCast_lt_aleph0)
    have hw : ∀ (g : treeOfColoring C) (hg : g ∈ p) (g' : treeOfColoring C) (hg' : g' ∈ p),
        g ≠ g' → ∃ α, ∃ hα : α < b,
        C.color α (dl g) (hα.trans_le (hdl g (hpL hg))) ≠
          C.color α (dl g') (hα.trans_le (hdl g' (hpL hg'))) := by
      intro g hg g' hg' hne
      by_contra hc'
      push Not at hc'
      exact hne (heq g (hpL hg) g' (hpL hg') hc')
    choose! wf hwlt hwd using hw
    let W : Set (Kappa κ) := (fun q => wf q.1 q.2) '' ((p ×ˢ p) ∩ {q | q.1 ≠ q.2})
    have hWfin : W.Finite := ((hpfin.prod hpfin).inter_of_left _).image _
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hμ0 Nat.cast_zero
    have hpnt : Nontrivial p := by
      rw [← Cardinal.one_lt_iff_nontrivial, hpc]
      exact_mod_cast (by omega : 1 < n + 1)
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩ := exists_pair_ne p
    have hWne : W.Nonempty :=
      ⟨_, ⟨(x, y), ⟨⟨hx, hy⟩, fun e => hxy (Subtype.ext e)⟩, rfl⟩⟩
    obtain ⟨a, haW, hamax'⟩ := hWfin.exists_maximal hWne
    have hamax : ∀ y ∈ W, y ≤ a := fun y hy => (le_total y a).elim id (hamax' hy)
    have hab : a < b := by
      obtain ⟨q, ⟨⟨hq1, hq2⟩, hq⟩, rfl⟩ := haW
      exact hwlt q.1 hq1 q.2 hq2 hq
    let ψ : p → Kappa (n : Cardinal.{w}) := fun g =>
      C.color a (dl g) (hab.trans_le (hdl g (hpL g.2)))
    have hψ : Function.Injective ψ := by
      rintro ⟨g, hg⟩ ⟨g', hg'⟩ e
      by_contra hne
      have hne' : g ≠ g' := fun h => hne (Subtype.ext h)
      have hle : wf g g' ≤ a := hamax _ ⟨(g, g'), ⟨⟨hg, hg'⟩, hne'⟩, rfl⟩
      exact hwd g hg g' hg' hne' (hC.color_eq_of_le _ _ e hle)
    have := Cardinal.mk_le_of_injective hψ
    rw [hpc, hKμ, Nat.cast_le] at this
    omega
end JardenShami
