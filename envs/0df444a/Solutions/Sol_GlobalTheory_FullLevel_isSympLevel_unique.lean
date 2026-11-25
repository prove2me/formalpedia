-- Prove2me | solution 1 for GlobalTheory.FullLevel.isSympLevel_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:51:44.424174+00:00
-- url     : https://prove2.me/submissions/9be99b58-def1-471d-a3bf-3fe76bf93361

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSympLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsFullSymplecticLevelStructureUniqueOfLevels
import Theorems.Thm_GlobalTheory_FullLevel_Uniq_mem_of_dvd
import Theorems.Thm_GlobalTheory_FullLevel_Uniq_mem_lcm
import Theorems.Thm_GlobalTheory_FullLevel_Uniq_ev_eq_iff
import Theorems.Thm_GlobalTheory_FullLevel_Uniq_ev_pow_eq
import Theorems.Thm_P2M_GlobalTheory_FullLevel_A_dvd_M__c65dcadf2e66
import Theorems.Thm_P2M_GlobalTheory_FullLevel_M__pos_df9b3d1f4b28
import Theorems.Thm_P2M_GlobalTheory_FullLevel_M_dvd_M__ccc9399a2d7f
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField GlobalTheory.FullLevel
open GlobalTheory GlobalTheory.FullLevel
open Uniq
namespace GlobalTheory.FullLevel
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} (l : Level H)
    {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
    (he : ∀ (g g' : Q) (c c' : kˣ), e l.M' g g' c → e l.M' g g' c' → c = c')
    {z : kˣ} (hz : IsPrimitiveRoot z l.M') {etaA eta ev ev' : D.La → Q}
    (h : IsSympLevel D act e l.M' z ev) (hi : Induces l etaA eta ev)
    (h' : IsSympLevel D act e l.M' z ev') (hi' : Induces l etaA eta ev') : ev = ev' := by
  have hM' := M'_pos l
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have hex : ∀ a, ∃ x, ev x = ev' a := fun a =>
    (h.2.2.2.1 _).1 ((h'.2.2.2.1 _).2 ⟨a, rfl⟩)
  choose g hg using hex
  have h1 : ∀ a, ∃ b, g a - a = l.A • b := fun a =>
    ev_pow_eq h hM' (A_dvd_M' l) (by rw [hg, hi'.1, hi.1])
  have h2 : ∀ c ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E), ∀ a : D.La, ∃ b, g (c • a) - c • a = l.M • b := by
    intro c hc a
    have hmem : c • a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) :=
      Submodule.smul_mem_smul hc Submodule.mem_top
    exact ev_pow_eq h hM' (M_dvd_M' l) (by rw [hg, hi'.2 _ hmem, hi.2 _ hmem])
  have h3 : ∀ a b, (l.M : ℤ) ∣ D.EF (g a) (g b) - D.EF a b := by
    intro a b
    have e1 := h.2.2.2.2 (g a) (g b)
    rw [hg, hg] at e1
    have e2 := he _ _ _ _ e1 (h'.2.2.2.2 a b)
    have e3 : z ^ (D.EF (g a) (g b) - D.EF a b) = 1 := by rw [zpow_sub, e2, mul_inv_cancel]
    exact (Int.natCast_dvd_natCast.2 (M_dvd_M' l)).trans ((hz.zpow_eq_one_iff_dvd _).1 e3)
  obtain ⟨n, hn, m, hm, hnm⟩ := Submodule.mem_sup.1 (show (1 : 𝓞 E) ∈ _ from l.coprime ▸ Submodule.mem_top)
  funext a
  have h4 : ∃ u, m • (g a - a) = l.M • u := by
    obtain ⟨b, hb⟩ := h2 m hm a
    obtain ⟨c, hc⟩ := (ev_eq_iff h (m • g a) (g (m • a))).1 (by rw [h.2.1, hg, hg, h'.2.1])
    obtain ⟨t, ht⟩ := M_dvd_M' l
    refine ⟨t • c + b, ?_⟩
    rw [smul_add, smul_smul, ← ht, ← hc, ← hb, smul_sub]
    abel
  have h5 : ∃ u, n • (g a - a) = l.M • u := by
    refine mem_of_dvd hM fun y => ?_
    obtain ⟨b, hb⟩ := h2 (H.bar n) (Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hn) y
    have h6 := h3 a (H.bar n • y)
    rw [sub_eq_iff_eq_add] at hb
    rw [hb, map_add, map_nsmul, nsmul_eq_mul, add_sub_assoc, dvd_add_right (dvd_mul_right _ _)] at h6
    rw [D.adj, map_sub, LinearMap.sub_apply]
    exact h6
  obtain ⟨u, hu⟩ := h4
  obtain ⟨v, hv⟩ := h5
  obtain ⟨b, hb⟩ := h1 a
  have h7 : g a - a = l.M • (v + u) := by rw [smul_add, ← hu, ← hv, ← add_smul, hnm, one_smul]
  rw [← hg]
  exact ((ev_eq_iff h _ _).2 (mem_lcm hM h7 hb)).symm
end GlobalTheory.FullLevel
