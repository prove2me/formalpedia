-- Prove2me | solution 1 for HarksKlimm.Consistency.three_load_witness
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:02:24.429001+00:00
-- url     : https://prove2.me/submissions/18a68651-95dc-49a0-b377-e20e7e6300f5

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_IsMonotonic

open scoped NNReal
open HarksKlimm.Consistency

theorem g79h_L1 (c : ℝ≥0 → ℝ) (hc : Continuous c) (ym tt : ℝ≥0) (hlt : ym < tt)
    (h0 : c ym < c 0) (h1 : c ym < c tt) :
    ∃ x y : ℝ≥0, 0 < x ∧ x < y ∧ c (y - x) < c y ∧ c y < c x := by
  have hym : 0 < ym := by
    rcases eq_or_ne ym 0 with h | h
    · rw [h] at h0; exact absurd h0 (lt_irrefl _)
    · exact pos_iff_ne_zero.mpr h
  set v : ℝ := (c ym + min (c 0) (c tt)) / 2 with hv
  have hv1 : c ym < v := by have := lt_min h0 h1; rw [hv]; linarith
  have hv2 : v < c 0 := by have := min_le_left (c 0) (c tt); rw [hv]; linarith
  have hv3 : v < c tt := by have := min_le_right (c 0) (c tt); rw [hv]; linarith
  set T : Set ℝ≥0 := Set.Icc ym tt ∩ {t | v ≤ c t} with hT
  have hTne : T.Nonempty := ⟨tt, ⟨hlt.le, le_rfl⟩, hv3.le⟩
  have hTcl : IsClosed T := isClosed_Icc.inter (isClosed_le continuous_const hc)
  have hTbdd : BddBelow T := ⟨ym, fun t ht => ht.1.1⟩
  set y := sInf T with hy
  have hyT : y ∈ T := hTcl.csInf_mem hTne hTbdd
  have hbelow : ∀ t, ym ≤ t → t < y → c t < v := by
    intro t ht1 ht2
    by_contra hge; push Not at hge
    have : t ∈ T := ⟨⟨ht1, (ht2.le.trans hyT.1.2)⟩, hge⟩
    exact absurd (csInf_le hTbdd this) (not_le.mpr ht2)
  have hymy : ym < y := by
    rcases hyT.1.1.lt_or_eq with h | h
    · exact h
    · have h2 : v ≤ c y := hyT.2
      rw [← h] at h2; linarith
  have hcy : c y = v := by
    refine le_antisymm ?_ hyT.2
    by_contra hgt; push Not at hgt
    have hev := hc.continuousAt.eventually (lt_mem_nhds hgt)
    obtain ⟨a, b, ⟨ha, hb⟩, hab⟩ := (mem_nhds_iff_exists_Ioo_subset' ⟨ym, hymy⟩ ⟨y + 1, lt_add_one y⟩).mp hev
    set t := max a ym
    obtain ⟨s, hs1, hs2⟩ := exists_between (max_lt ha hymy)
    have h1 := hbelow s (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hs1)) hs2
    have h2 := hab ⟨lt_of_le_of_lt (le_max_left _ _) hs1, lt_trans hs2 hb⟩
    exact absurd h2 (not_lt.mpr h1.le)
  -- small x with c x > v
  have hev0 := hc.continuousAt.eventually (lt_mem_nhds hv2)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev0
  set d := y - ym with hd
  have hdpos : 0 < d := tsub_pos_of_lt hymy
  set x : ℝ≥0 := min (⟨ε / 2, by positivity⟩ : ℝ≥0) d with hx
  have hxpos : 0 < x := lt_min (by show (0:ℝ) < ε / 2; positivity) hdpos
  have hxd : x ≤ d := min_le_right _ _
  have hxy : x < y := lt_of_le_of_lt hxd (tsub_lt_self (lt_trans hym hymy) hym)
  refine ⟨x, y, hxpos, hxy, ?_, ?_⟩
  · rw [hcy]
    apply hbelow
    · have h1 : x + ym ≤ y := (le_tsub_iff_right hymy.le).mp hxd
      exact (le_tsub_iff_left hxy.le).mpr h1
    · exact tsub_lt_self (lt_trans hxpos hxy) hxpos
  · rw [hcy]
    have hxe : (x : ℝ) ≤ ε / 2 := by
      have := min_le_left (⟨ε / 2, by positivity⟩ : ℝ≥0) d
      exact_mod_cast this
    have : dist x 0 < ε := by
      rw [NNReal.dist_eq]; simp only [NNReal.coe_zero, sub_zero]
      rw [NNReal.abs_eq]; linarith
    exact hball this

theorem solution (c : ℝ≥0 → ℝ) (hc : Continuous c)
    (hn : ¬ IsMonotonic c) :
    ∃ x y : ℝ≥0, 0 < x ∧ x < y ∧
      ((c (y - x) < c y ∧ c y < c x) ∨
       (c x < c y ∧ c y < c (y - x))) := by
  by_contra H
  have P1 : ∀ u t, u < t → c u < c 0 → c t ≤ c u := by
    intro u t hut hu
    by_contra h; push Not at h
    obtain ⟨x, y, hx, hxy, h1, h2⟩ := g79h_L1 c hc u t hut hu h
    exact H ⟨x, y, hx, hxy, Or.inl ⟨h1, h2⟩⟩
  have P2 : ∀ u t, u < t → c 0 < c u → c u ≤ c t := by
    intro u t hut hu
    by_contra h; push Not at h
    obtain ⟨x, y, hx, hxy, h1, h2⟩ := g79h_L1 (fun z => -c z) hc.neg u t hut (by linarith) (by linarith)
    exact H ⟨x, y, hx, hxy, Or.inr ⟨by linarith, by linarith⟩⟩
  apply hn
  by_cases hup : ∀ t, c 0 ≤ c t
  · left
    intro a b hab
    rcases (hup a).lt_or_eq with h | h
    · rcases hab.lt_or_eq with h' | h'
      · exact P2 a b h' h
      · rw [h']
    · rw [← h]; exact hup b
  · push Not at hup
    obtain ⟨w, hw⟩ := hup
    have hdown : ∀ t, c t ≤ c 0 := by
      intro t; by_contra ht; push Not at ht
      rcases lt_trichotomy t w with h | h | h
      · have := P2 t w h ht; linarith
      · rw [h] at ht; linarith
      · have := P1 w t h hw; linarith
    right
    intro a b hab
    rcases (hdown a).lt_or_eq with h | h
    · rcases hab.lt_or_eq with h' | h'
      · exact P1 a b h' h
      · rw [h']
    · rw [h]; exact hdown b
