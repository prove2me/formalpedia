-- Prove2me | solution 1 for HogFarm.SalesAlloc.attainment
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T17:14:56.643337+00:00
-- url     : https://prove2.me/submissions/f493826a-3bbe-444f-a48e-3f7277e35093

import Mathlib
import Definitions.Def_HogFarm_SalesAlloc_Model

set_option autoImplicit false

namespace HogAtt

open HogFarm.SalesAlloc

/-- Chord facts of a holding level `L` for the marginal value `v` on `[0, cap]`. -/
def LF (G : ℝ → ℝ) (cap v L : ℝ) : Prop :=
  0 ≤ L ∧ L ≤ cap ∧
  (∀ Z, 0 ≤ Z → Z ≤ cap → G Z ≤ G L + v * (Z - L)) ∧
  (∀ x y, 0 ≤ x → x ≤ y → y ≤ L → G x ≤ G y - v * (y - x)) ∧
  (∀ x y, L ≤ x → x ≤ y → y ≤ cap → G y ≤ G x + v * (y - x))

lemma marg0 {G : ℝ → ℝ} {v Z δ : ℝ} (h : MarginLE G v Z) (hδ : 0 ≤ δ) :
    G (Z + δ) - G Z ≤ v * δ := by
  rcases hδ.eq_or_lt with h0 | h0
  · rw [← h0]; simp
  · exact h δ h0

lemma conc_min {G : ℝ → ℝ} (hG : ConcaveOn ℝ (Set.Ici 0) G) (v : ℝ) {x y z : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) :
    min (G x - v * x) (G z - v * z) ≤ G y - v * y := by
  rcases (hxy.trans hyz).eq_or_lt with hxz | hxz
  · have hy : y = x := le_antisymm (by rw [hxz]; exact hyz) hxy
    rw [hy]
    exact min_le_left _ _
  · have hzx : 0 < z - x := sub_pos.2 hxz
    have hne : z - x ≠ 0 := hzx.ne'
    obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = (z - y) / (z - x) := ⟨_, rfl⟩
    obtain ⟨b, hb_def⟩ : ∃ b : ℝ, b = (y - x) / (z - x) := ⟨_, rfl⟩
    have ha : 0 ≤ a := by rw [ha_def]; exact div_nonneg (sub_nonneg.2 hyz) hzx.le
    have hb : 0 ≤ b := by rw [hb_def]; exact div_nonneg (sub_nonneg.2 hxy) hzx.le
    have hab : a + b = 1 := by
      rw [ha_def, hb_def, ← add_div, div_eq_one_iff_eq hne]; ring
    have hy : a * x + b * z = y := by
      rw [ha_def, hb_def]; field_simp; ring
    have key := hG.2 (Set.mem_Ici.2 hx) (Set.mem_Ici.2 (hx.trans (hxy.trans hyz))) ha hb hab
    simp only [smul_eq_mul] at key
    rw [hy] at key
    have h1 : a * min (G x - v * x) (G z - v * z) ≤ a * (G x - v * x) :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) ha
    have h2 : b * min (G x - v * x) (G z - v * z) ≤ b * (G z - v * z) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hb
    have hM : a * min (G x - v * x) (G z - v * z) + b * min (G x - v * x) (G z - v * z)
        = min (G x - v * x) (G z - v * z) := by rw [← add_mul, hab, one_mul]
    have hvy : v * y = a * (v * x) + b * (v * z) := by rw [← hy]; ring
    linarith

lemma lvl {G : ℝ → ℝ} (hG : ConcaveOn ℝ (Set.Ici 0) G) {m v cap : ℝ} (hvm : v ≤ m)
    (hcap : 0 ≤ cap) (hb : ∀ Z : ℝ, 0 ≤ Z → MarginLE G m Z) :
    LF G cap v (levelOf G cap v) := by
  obtain ⟨S, hS⟩ : ∃ S : Set ℝ, S = {Z : ℝ | 0 ≤ Z ∧ MarginLE G v Z} := ⟨_, rfl⟩
  have hL : levelOf G cap v = sInf (insert cap S) := by rw [hS]; rfl
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = levelOf G cap v := ⟨_, rfl⟩
  rw [← hLdef]
  rw [← hLdef] at hL
  have hmem : ∀ z, z ∈ insert cap S → 0 ≤ z := by
    intro z hz
    rcases hz with hz | hz
    · rw [hz]; exact hcap
    · rw [hS] at hz; exact hz.1
  have hbdd : BddBelow (insert cap S) := ⟨0, fun z hz => hmem z hz⟩
  have hne : (insert cap S).Nonempty := ⟨cap, Set.mem_insert _ _⟩
  have hL0 : 0 ≤ L := by rw [hL]; exact le_csInf hne hmem
  have hLc : L ≤ cap := by rw [hL]; exact csInf_le hbdd (Set.mem_insert _ _)
  have hLS : ∀ w, 0 ≤ w → MarginLE G v w → L ≤ w := fun w hw hm => by
    rw [hL]; exact csInf_le hbdd (Set.mem_insert_of_mem _ (by rw [hS]; exact ⟨hw, hm⟩))
  have hmax : ∀ Z, 0 ≤ Z → Z ≤ cap → G Z - v * Z ≤ G L - v * L := by
    intro Z hZ0 hZc
    rcases lt_trichotomy Z L with hZL | hZL | hZL
    · have hLpos : 0 < L := lt_of_le_of_lt hZ0 hZL
      have hge : ∀ w, Z < w → w < L → G Z - v * Z ≤ G w - v * w := by
        intro w hZw hwL
        have hw0 : 0 ≤ w := hZ0.trans hZw.le
        have hnot : ¬ MarginLE G v w := fun hm => absurd (hLS w hw0 hm) (not_le.2 hwL)
        unfold MarginLE at hnot
        push_neg at hnot
        obtain ⟨δ, hδ, hgt⟩ := hnot
        have hc := conc_min hG v hZ0 hZw.le (le_add_of_nonneg_right hδ.le : w ≤ w + δ)
        rcases le_total (G Z - v * Z) (G (w + δ) - v * (w + δ)) with h | h
        · rw [min_eq_left h] at hc; exact hc
        · rw [min_eq_right h] at hc; linarith
      have hcont : ContinuousAt G L := by
        have := hG.continuousOn_interior
        rw [interior_Ici] at this
        exact this.continuousAt (Ioi_mem_nhds hLpos)
      have hcont' : ContinuousAt (fun w => G w - v * w) L :=
        hcont.sub (continuousAt_const.mul continuousAt_id)
      have ht : Filter.Tendsto (fun w => G w - v * w) (nhdsWithin L (Set.Iio L))
          (nhds (G L - v * L)) :=
        hcont'.tendsto.mono_left nhdsWithin_le_nhds
      apply ge_of_tendsto ht
      filter_upwards [Ioo_mem_nhdsLT hZL] with w hw
      exact hge w hw.1 hw.2
    · rw [hZL]
    · by_contra hcon
      push_neg at hcon
      obtain ⟨gap, hgap⟩ : ∃ g : ℝ, g = (G Z - v * Z) - (G L - v * L) := ⟨_, rfl⟩
      have hgap0 : 0 < gap := by linarith
      have hK0 : 0 < m - v + 1 := by linarith
      obtain ⟨ε, hε⟩ : ∃ e : ℝ, e = min (Z - L) (gap / (m - v + 1)) := ⟨_, rfl⟩
      have hε0 : 0 < ε := by rw [hε]; exact lt_min (by linarith) (div_pos hgap0 hK0)
      have hlt : sInf (insert cap S) < L + ε := by rw [← hL]; linarith
      obtain ⟨w, hwS, hwlt⟩ := exists_lt_of_csInf_lt hne hlt
      have hεZ : ε ≤ Z - L := by rw [hε]; exact min_le_left _ _
      have hwZ : w < Z := by linarith
      have hwS' : w ∈ S := by
        rcases hwS with h | h
        · exfalso; rw [h] at hwZ; linarith
        · exact h
      rw [hS] at hwS'
      obtain ⟨hw0, hwm⟩ := hwS'
      have hLw : L ≤ w := hLS w hw0 hwm
      have h1 := hwm (Z - w) (by linarith)
      rw [show w + (Z - w) = Z by ring] at h1
      have h2 := marg0 (hb L hL0) (show 0 ≤ w - L by linarith)
      rw [show L + (w - L) = w by ring] at h2
      have h3 : (m - v) * (w - L) ≤ (m - v + 1) * (w - L) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      have h4 : (m - v + 1) * (w - L) < (m - v + 1) * ε :=
        mul_lt_mul_of_pos_left (by linarith) hK0
      have h5 : (m - v + 1) * ε ≤ (m - v + 1) * (gap / (m - v + 1)) :=
        mul_le_mul_of_nonneg_left (by rw [hε]; exact min_le_right _ _) hK0.le
      have h6 : (m - v + 1) * (gap / (m - v + 1)) = gap := mul_div_cancel₀ gap hK0.ne'
      linarith
  refine ⟨hL0, hLc, ?_, ?_, ?_⟩
  · intro Z hZ0 hZc
    have := hmax Z hZ0 hZc
    linarith
  · intro x y hx hxy hyL
    have hc := conc_min hG v hx hxy hyL
    have hx' := hmax x hx (hxy.trans (hyL.trans hLc))
    rw [min_eq_left hx'] at hc
    linarith
  · intro x y hLx hxy hyc
    have hc := conc_min hG v hL0 hLx hxy
    have hy' := hmax y (hL0.trans (hLx.trans hxy)) hyc
    rw [min_eq_right hy'] at hc
    linarith

lemma lvl_anti (G : ℝ → ℝ) {cap v w : ℝ} (hcap : 0 ≤ cap) (hvw : v ≤ w) :
    levelOf G cap w ≤ levelOf G cap v := by
  unfold levelOf
  apply csInf_le_csInf
  · refine ⟨0, ?_⟩
    intro z hz
    rcases hz with hz | hz
    · rw [hz]; exact hcap
    · exact hz.1
  · exact ⟨cap, Set.mem_insert _ _⟩
  · intro z hz
    rcases hz with hz | hz
    · rw [hz]; exact Set.mem_insert _ _
    · refine Set.mem_insert_of_mem _ ⟨hz.1, fun δ hδ => (hz.2 δ hδ).trans ?_⟩
      exact mul_le_mul_of_nonneg_right hvw hδ.le

lemma case1a {P : Prices} {q α s1 s2 : ℝ} {G : ℝ → ℝ} {L0 : ℝ}
    (hp12 : P.p1 ≤ P.p2) (hs1 : 0 ≤ s1) (hs2 : 0 ≤ s2) (hq : 0 < q)
    (hB : P.pC + P.cP < P.p2) (hA : (1 - α) * P.pC + P.cP < P.p1)
    (h0 : LF G (s1 + s2) P.p1 L0)
    (hb : ∀ x y, 0 ≤ x → x ≤ y → G y ≤ G x + P.p2 * (y - x)) :
    OnePeriodOptimal P q α s1 s2 G 0 0 (min s1 L0) 0 := by
  obtain ⟨hL0, hLc, hF, hMo, -⟩ := h0
  refine ⟨⟨le_rfl, le_rfl, le_min hs1 hL0, le_rfl, by linarith,
    by linarith [min_le_left s1 L0], by linarith⟩, ?_⟩
  rintro a b c d ⟨ha, hb0, hc, hd, hab, hac, hbd⟩
  simp only [onePeriodObjective, add_zero]
  have hs1ac : 0 ≤ s1 - a - c := by linarith
  have k1 := mul_nonneg (sub_nonneg.2 hA.le) ha
  have k2 := mul_nonneg (sub_nonneg.2 hB.le) hb0
  have k3 := mul_nonneg (sub_nonneg.2 hp12) hd
  have k4 := mul_nonneg (sub_nonneg.2 hp12) hs1ac
  have k5 := mul_nonneg (sub_nonneg.2 hp12) ha
  rcases le_total L0 s1 with h | h
  · rw [min_eq_right h]
    linarith [hF (c + d) (by linarith) (by linarith)]
  · rw [min_eq_left h]
    rcases le_total (c + d) s1 with hZ | hZ
    · linarith [hMo (c + d) s1 (by linarith) hZ h]
    · linarith [hb s1 (c + d) hs1 hZ]

lemma case1b {P : Prices} {q α s1 s2 : ℝ} {G : ℝ → ℝ} {L1 L0 : ℝ}
    (hα0 : 0 < α) (hpC : 0 ≤ P.pC) (hp12 : P.p1 ≤ P.p2) (hs1 : 0 ≤ s1) (hs2 : 0 ≤ s2)
    (hq : 0 < q)
    (hB : P.pC + P.cP < P.p2) (hA : P.p1 ≤ (1 - α) * P.pC + P.cP)
    (h1 : LF G (s1 + s2) ((1 - α) * P.pC + P.cP) L1)
    (h0 : LF G (s1 + s2) P.p1 L0) (h10 : L1 ≤ L0)
    (hb : ∀ x y, 0 ≤ x → x ≤ y → G y ≤ G x + P.p2 * (y - x)) :
    OnePeriodOptimal P q α s1 s2 G (min (max (s1 - L1) 0) q) 0
      (min (s1 - min (max (s1 - L1) 0) q) L0) 0 := by
  obtain ⟨hL1, hL1c, hF1, hMo1, hAn1⟩ := h1
  obtain ⟨hL0, hL0c, hF0, hMo0, -⟩ := h0
  have hf12 : (1 - α) * P.pC + P.cP ≤ P.pC + P.cP := by nlinarith [mul_nonneg hα0.le hpC]
  constructor
  · rcases le_total s1 L1 with h | h
    · rw [max_eq_right (by linarith : s1 - L1 ≤ 0), min_eq_left hq.le]
      simp only [sub_zero]
      rw [min_eq_left (h.trans h10)]
      exact ⟨le_rfl, le_rfl, hs1, le_rfl, by linarith, by linarith, by linarith⟩
    · rw [max_eq_left (by linarith : (0:ℝ) ≤ s1 - L1)]
      rcases le_total (s1 - L1) q with h' | h'
      · rw [min_eq_left h', sub_sub_cancel, min_eq_left h10]
        exact ⟨by linarith, le_rfl, hL1, le_rfl, by linarith, by linarith, by linarith⟩
      · rw [min_eq_right h']
        rcases le_total (s1 - q) L0 with h'' | h''
        · rw [min_eq_left h'']
          exact ⟨hq.le, le_rfl, by linarith, le_rfl, by linarith, by linarith, by linarith⟩
        · rw [min_eq_right h'']
          exact ⟨hq.le, le_rfl, hL0, le_rfl, by linarith, by linarith, by linarith⟩
  rintro a b c d ⟨ha, hb0, hc, hd, hab, hac, hbd⟩
  simp only [onePeriodObjective, add_zero]
  have hs1ac : 0 ≤ s1 - a - c := by linarith
  have hqa : 0 ≤ q - a := by linarith
  have cA : 0 ≤ (1 - α) * P.pC + P.cP - P.p1 := by linarith
  have cB : 0 ≤ P.p2 - (P.pC + P.cP) := by linarith
  have c2f1 : 0 ≤ P.p2 - ((1 - α) * P.pC + P.cP) := by linarith
  have c21 : 0 ≤ P.p2 - P.p1 := by linarith
  have k1 := mul_nonneg cA hs1ac
  have k2 := mul_nonneg cA hqa
  have k3 := mul_nonneg cB hb0
  have k4 := mul_nonneg c2f1 hd
  have k5 := mul_nonneg c2f1 ha
  have k6 := mul_nonneg c21 hs1ac
  have k7 := mul_nonneg c21 hd
  rcases le_total s1 L1 with h | h
  · rw [max_eq_right (by linarith : s1 - L1 ≤ 0), min_eq_left hq.le]
    simp only [sub_zero]
    rw [min_eq_left (h.trans h10)]
    rcases le_total (c + d) s1 with hZ | hZ
    · linarith [hMo1 (c + d) s1 (by linarith) hZ h]
    · linarith [hb s1 (c + d) hs1 hZ]
  · rw [max_eq_left (by linarith : (0:ℝ) ≤ s1 - L1)]
    rcases le_total (s1 - L1) q with h' | h'
    · rw [min_eq_left h', sub_sub_cancel, min_eq_left h10]
      linarith [hF1 (c + d) (by linarith) (by linarith)]
    · rw [min_eq_right h']
      rcases le_total (s1 - q) L0 with h'' | h''
      · rw [min_eq_left h'']
        rcases le_total (s1 - q) (c + d) with hZ | hZ
        · linarith [hAn1 (s1 - q) (c + d) (by linarith) hZ (by linarith)]
        · linarith [hMo0 (c + d) (s1 - q) (by linarith) hZ h'']
      · rw [min_eq_right h'']
        linarith [hF0 (c + d) (by linarith) (by linarith)]

lemma case2a {P : Prices} {q α s1 s2 : ℝ} {G : ℝ → ℝ} {L0 L2 : ℝ}
    (hp12 : P.p1 ≤ P.p2) (hs1 : 0 ≤ s1) (hs2 : 0 ≤ s2) (hq : 0 < q)
    (hB : P.p2 ≤ P.pC + P.cP) (hA : (1 - α) * P.pC + P.cP < P.p1)
    (h0 : LF G (s1 + s2) P.p1 L0) (h2 : LF G (s1 + s2) P.p2 L2) (h20 : L2 ≤ L0)
    (hb : ∀ x y, 0 ≤ x → x ≤ y → G y ≤ G x + (P.pC + P.cP) * (y - x)) :
    OnePeriodOptimal P q α s1 s2 G 0 (min s2 q) (min s1 L0)
      (min (max (s2 - q) 0) (max (L2 - min s1 L0) 0)) := by
  obtain ⟨hL0, hL0c, hF0, hMo0, -⟩ := h0
  obtain ⟨hL2, hL2c, hF2, hMo2, hAn2⟩ := h2
  constructor
  · refine ⟨le_rfl, le_min hs2 hq.le, le_min hs1 hL0,
      le_min (le_max_right _ _) (le_max_right _ _), by linarith [min_le_right s2 q],
      by linarith [min_le_left s1 L0], ?_⟩
    rcases le_total s2 q with hsq | hsq
    · rw [min_eq_left hsq, max_eq_right (by linarith : s2 - q ≤ 0),
        min_eq_left (le_max_right (L2 - min s1 L0) 0)]
      linarith
    · rw [min_eq_right hsq, max_eq_left (by linarith : (0:ℝ) ≤ s2 - q)]
      linarith [min_le_left (s2 - q) (max (L2 - min s1 L0) 0)]
  rintro a b c d ⟨ha, hb0, hc, hd, hab, hac, hbd⟩
  simp only [onePeriodObjective]
  have hs1ac : 0 ≤ s1 - a - c := by linarith
  have hqab : 0 ≤ q - a - b := by linarith
  have hs2bd : 0 ≤ s2 - b - d := by linarith
  have cA : 0 ≤ P.p1 - ((1 - α) * P.pC + P.cP) := by linarith
  have cB : 0 ≤ P.pC + P.cP - P.p2 := by linarith
  have c21 : 0 ≤ P.p2 - P.p1 := by linarith
  have cf1 : 0 ≤ P.pC + P.cP - P.p1 := by linarith
  have k1 := mul_nonneg cA ha
  have k2 := mul_nonneg cB hs2bd
  have k3 := mul_nonneg cB hd
  have k4 := mul_nonneg c21 hd
  have k5 := mul_nonneg cB hqab
  have k6 := mul_nonneg cB ha
  have k7 := mul_nonneg cf1 hs1ac
  have k8 := mul_nonneg cf1 ha
  have k9 := mul_nonneg c21 hs1ac
  have k10 := mul_nonneg c21 ha
  rcases le_total s2 q with hsq | hsq
  · rw [min_eq_left hsq, max_eq_right (by linarith : s2 - q ≤ 0),
      min_eq_left (le_max_right (L2 - min s1 L0) 0), add_zero]
    rcases le_total L0 s1 with h | h
    · rw [min_eq_right h]
      linarith [hF0 (c + d) (by linarith) (by linarith)]
    · rw [min_eq_left h]
      rcases le_total (c + d) s1 with hZ | hZ
      · linarith [hMo0 (c + d) s1 (by linarith) hZ h]
      · linarith [hb s1 (c + d) hs1 hZ]
  · rw [min_eq_right hsq, max_eq_left (by linarith : (0:ℝ) ≤ s2 - q)]
    rcases le_or_gt L2 (min s1 L0) with hz | hz
    · rw [max_eq_right (by linarith : L2 - min s1 L0 ≤ 0),
        min_eq_right (by linarith : (0:ℝ) ≤ s2 - q), add_zero]
      rcases le_total L0 s1 with h | h
      · rw [min_eq_right h]
        linarith [hF0 (c + d) (by linarith) (by linarith)]
      · rw [min_eq_left h] at hz ⊢
        rcases le_total (c + d) s1 with hZ | hZ
        · linarith [hMo0 (c + d) s1 (by linarith) hZ h]
        · linarith [hAn2 s1 (c + d) hz hZ (by linarith)]
    · have hs1L0 : s1 ≤ L0 := by
        by_contra hcon
        push_neg at hcon
        rw [min_eq_right hcon.le] at hz
        linarith
      rw [min_eq_left hs1L0] at hz ⊢
      rw [max_eq_left (by linarith : (0:ℝ) ≤ L2 - s1)]
      rcases le_total (s2 - q) (L2 - s1) with hd' | hd'
      · rw [min_eq_left hd']
        rcases le_total (s1 + (s2 - q)) (c + d) with hZ | hZ
        · linarith [hb (s1 + (s2 - q)) (c + d) (by linarith) hZ]
        · linarith [hMo2 (c + d) (s1 + (s2 - q)) (by linarith) hZ (by linarith)]
      · rw [min_eq_right hd', show s1 + (L2 - s1) = L2 by ring]
        linarith [hF2 (c + d) (by linarith) (by linarith)]

lemma case2b {P : Prices} {q α s1 s2 : ℝ} {G : ℝ → ℝ} {L1 L0 L2 : ℝ}
    (hα0 : 0 < α) (hpC : 0 ≤ P.pC) (hp12 : P.p1 ≤ P.p2) (hs1 : 0 ≤ s1) (hs2 : 0 ≤ s2)
    (hq : 0 < q)
    (hB : P.p2 ≤ P.pC + P.cP) (hA : 0 ≤ (1 - α) * P.pC + P.cP - P.p1)
    (hAB : (1 - α) * P.pC + P.cP - P.p1 ≤ P.pC + P.cP - P.p2)
    (h1 : LF G (s1 + s2) ((1 - α) * P.pC + P.cP) L1)
    (h0 : LF G (s1 + s2) P.p1 L0) (h2 : LF G (s1 + s2) P.p2 L2)
    (h10 : L1 ≤ L0) (h20 : L2 ≤ L0)
    (hb : ∀ x y, 0 ≤ x → x ≤ y → G y ≤ G x + (P.pC + P.cP) * (y - x)) :
    OnePeriodOptimal P q α s1 s2 G (min (max (s1 - L1) 0) (max (q - s2) 0)) (min s2 q)
      (min (max (s1 - min (max (s1 - L1) 0) (max (q - s2) 0)) 0) L0)
      (min (max (s2 - q) 0)
        (max (L2 - min (max (s1 - min (max (s1 - L1) 0) (max (q - s2) 0)) 0) L0) 0)) := by
  obtain ⟨hL1, hL1c, hF1, hMo1, hAn1⟩ := h1
  obtain ⟨hL0, hL0c, hF0, hMo0, -⟩ := h0
  obtain ⟨hL2, hL2c, hF2, hMo2, hAn2⟩ := h2
  have hf12 : (1 - α) * P.pC + P.cP ≤ P.pC + P.cP := by nlinarith [mul_nonneg hα0.le hpC]
  constructor
  · rcases le_total q s2 with hqs | hqs
    · rw [max_eq_right (by linarith : q - s2 ≤ 0),
        min_eq_right (le_max_right (s1 - L1) 0)]
      simp only [sub_zero]
      rw [max_eq_left hs1,
        min_eq_right hqs, max_eq_left (by linarith : (0:ℝ) ≤ s2 - q)]
      refine ⟨le_rfl, hq.le, le_min hs1 hL0, le_min (by linarith) (le_max_right _ _),
        by linarith, by linarith [min_le_left s1 L0], ?_⟩
      linarith [min_le_left (s2 - q) (max (L2 - min s1 L0) 0)]
    · rw [max_eq_left (by linarith : (0:ℝ) ≤ q - s2), min_eq_left hqs,
        max_eq_right (by linarith : s2 - q ≤ 0)]
      have e0 : ∀ u : ℝ, min (0 : ℝ) (max u 0) = 0 := fun u => min_eq_left (le_max_right u 0)
      rw [e0]
      rcases le_total s1 L1 with h | h
      · rw [max_eq_right (by linarith : s1 - L1 ≤ 0), min_eq_left (by linarith : (0:ℝ) ≤ q - s2)]
        simp only [sub_zero]
        rw [max_eq_left hs1, min_eq_left (h.trans h10)]
        exact ⟨le_rfl, hs2, hs1, le_rfl, by linarith, by linarith, by linarith⟩
      · rw [max_eq_left (by linarith : (0:ℝ) ≤ s1 - L1)]
        rcases le_total (s1 - L1) (q - s2) with h' | h'
        · rw [min_eq_left h', sub_sub_cancel, max_eq_left hL1, min_eq_left h10]
          exact ⟨by linarith, hs2, hL1, le_rfl, by linarith, by linarith, by linarith⟩
        · rw [min_eq_right h', max_eq_left (by linarith : (0:ℝ) ≤ s1 - (q - s2))]
          rcases le_total (s1 - (q - s2)) L0 with h'' | h''
          · rw [min_eq_left h'']
            exact ⟨by linarith, hs2, by linarith, le_rfl, by linarith, by linarith, by linarith⟩
          · rw [min_eq_right h'']
            exact ⟨by linarith, hs2, hL0, le_rfl, by linarith, by linarith, by linarith⟩
  rintro a b c d ⟨ha, hb0, hc, hd, hab, hac, hbd⟩
  simp only [onePeriodObjective]
  have hs1ac : 0 ≤ s1 - a - c := by linarith
  have hqab : 0 ≤ q - a - b := by linarith
  have hs2bd : 0 ≤ s2 - b - d := by linarith
  have hs2b : 0 ≤ s2 - b := by linarith
  have cA := hA
  have cB : 0 ≤ P.pC + P.cP - P.p2 := by linarith
  have cBA : 0 ≤ (P.pC + P.cP - P.p2) - ((1 - α) * P.pC + P.cP - P.p1) := by linarith
  have c21 : 0 ≤ P.p2 - P.p1 := by linarith
  have cf1 : 0 ≤ P.pC + P.cP - P.p1 := by linarith
  have cff : 0 ≤ P.pC + P.cP - ((1 - α) * P.pC + P.cP) := by linarith
  have k1 := mul_nonneg cBA ha
  have k2 := mul_nonneg cB hqab
  have k3 := mul_nonneg c21 hd
  have k4 := mul_nonneg c21 hs1ac
  have k5 := mul_nonneg c21 ha
  have k6 := mul_nonneg cB hs2bd
  have k7 := mul_nonneg cf1 hs1ac
  have k8 := mul_nonneg cff ha
  have k9 := mul_nonneg cff hd
  have k10 := mul_nonneg cA hs1ac
  have k11 := mul_nonneg cA hqab
  have k12 := mul_nonneg cBA hs2b
  rcases le_total q s2 with hqs | hqs
  · rw [max_eq_right (by linarith : q - s2 ≤ 0),
      min_eq_right (le_max_right (s1 - L1) 0)]
    simp only [sub_zero]
    rw [max_eq_left hs1,
      min_eq_right hqs, max_eq_left (by linarith : (0:ℝ) ≤ s2 - q)]
    rcases le_or_gt L2 (min s1 L0) with hz | hz
    · rw [max_eq_right (by linarith : L2 - min s1 L0 ≤ 0),
        min_eq_right (by linarith : (0:ℝ) ≤ s2 - q), add_zero]
      rcases le_total L0 s1 with h | h
      · rw [min_eq_right h]
        linarith [hF0 (c + d) (by linarith) (by linarith)]
      · rw [min_eq_left h] at hz ⊢
        rcases le_total (c + d) s1 with hZ | hZ
        · linarith [hMo0 (c + d) s1 (by linarith) hZ h]
        · linarith [hAn2 s1 (c + d) hz hZ (by linarith)]
    · have hs1L0 : s1 ≤ L0 := by
        by_contra hcon
        push_neg at hcon
        rw [min_eq_right hcon.le] at hz
        linarith
      rw [min_eq_left hs1L0] at hz ⊢
      rw [max_eq_left (by linarith : (0:ℝ) ≤ L2 - s1)]
      rcases le_total (s2 - q) (L2 - s1) with hd' | hd'
      · rw [min_eq_left hd']
        rcases le_total (s1 + (s2 - q)) (c + d) with hZ | hZ
        · linarith [hb (s1 + (s2 - q)) (c + d) (by linarith) hZ]
        · linarith [hMo2 (c + d) (s1 + (s2 - q)) (by linarith) hZ (by linarith)]
      · rw [min_eq_right hd', show s1 + (L2 - s1) = L2 by ring]
        linarith [hF2 (c + d) (by linarith) (by linarith)]
  · rw [max_eq_left (by linarith : (0:ℝ) ≤ q - s2), min_eq_left hqs,
      max_eq_right (by linarith : s2 - q ≤ 0)]
    have e0 : ∀ u : ℝ, min (0 : ℝ) (max u 0) = 0 := fun u => min_eq_left (le_max_right u 0)
    rw [e0, add_zero]
    rcases le_total s1 L1 with h | h
    · rw [max_eq_right (by linarith : s1 - L1 ≤ 0), min_eq_left (by linarith : (0:ℝ) ≤ q - s2)]
      simp only [sub_zero]
      rw [max_eq_left hs1, min_eq_left (h.trans h10)]
      rcases le_total (c + d) s1 with hZ | hZ
      · linarith [hMo1 (c + d) s1 (by linarith) hZ h]
      · linarith [hb s1 (c + d) hs1 hZ]
    · rw [max_eq_left (by linarith : (0:ℝ) ≤ s1 - L1)]
      rcases le_total (s1 - L1) (q - s2) with h' | h'
      · rw [min_eq_left h', sub_sub_cancel, max_eq_left hL1, min_eq_left h10]
        linarith [hF1 (c + d) (by linarith) (by linarith)]
      · rw [min_eq_right h', max_eq_left (by linarith : (0:ℝ) ≤ s1 - (q - s2))]
        rcases le_total (s1 - (q - s2)) L0 with h'' | h''
        · rw [min_eq_left h'']
          rcases le_total (s1 - (q - s2)) (c + d) with hZ | hZ
          · linarith [hAn1 (s1 - (q - s2)) (c + d) (by linarith) hZ (by linarith)]
          · linarith [hMo0 (c + d) (s1 - (q - s2)) (by linarith) hZ h'']
        · rw [min_eq_right h'']
          linarith [hF0 (c + d) (by linarith) (by linarith)]

end HogAtt

open HogFarm.SalesAlloc in
theorem solution (P : Prices) (q α s1 s2 : ℝ) (G : ℝ → ℝ)
    (hq : 0 < q) (hα0 : 0 < α) (hα1 : α < 1)
    (hp1 : 0 ≤ P.p1) (hp12 : P.p1 ≤ P.p2) (hpC : 0 ≤ P.pC)
    (hcP : 0 ≤ P.cP) (hs1 : 0 ≤ s1) (hs2 : 0 ≤ s2)
    (hG : ConcaveOn ℝ (Set.Ici 0) G)
    (hbound : ∀ Z : ℝ, 0 ≤ Z → MarginLE G (max (P.pC + P.cP) P.p2) Z) :
    let f1 := (1 - α) * P.pC + P.cP
    let f2 := P.pC + P.cP
    let zl1 := levelOf G (s1 + s2) f1
    let zb1 := levelOf G (s1 + s2) P.p1
    let Zb2 := levelOf G (s1 + s2) P.p2
    (f2 < P.p2 → f1 < P.p1 →
      OnePeriodOptimal P q α s1 s2 G 0 0 (min s1 zb1) 0) ∧
    (f2 < P.p2 → P.p1 ≤ f1 →
      let y1 := min (max (s1 - zl1) 0) q
      OnePeriodOptimal P q α s1 s2 G y1 0 (min (s1 - y1) zb1) 0) ∧
    (P.p2 ≤ f2 → f1 < P.p1 →
      let z1 := min s1 zb1
      OnePeriodOptimal P q α s1 s2 G 0 (min s2 q) z1
        (min (max (s2 - q) 0) (max (Zb2 - z1) 0))) ∧
    (P.p2 ≤ f2 → 0 ≤ f1 - P.p1 → f1 - P.p1 ≤ f2 - P.p2 →
      let y1 := min (max (s1 - zl1) 0) (max (q - s2) 0)
      let z1 := min (max (s1 - y1) 0) zb1
      OnePeriodOptimal P q α s1 s2 G y1 (min s2 q) z1
        (min (max (s2 - q) 0) (max (Zb2 - z1) 0))) := by
  intro f1 f2 zl1 zb1 Zb2
  have hcap : 0 ≤ s1 + s2 := add_nonneg hs1 hs2
  have hf12 : (1 - α) * P.pC + P.cP ≤ P.pC + P.cP := by nlinarith [mul_nonneg hα0.le hpC]
  have hbm : ∀ x y, 0 ≤ x → x ≤ y →
      G y ≤ G x + max (P.pC + P.cP) P.p2 * (y - x) := fun x y hx hxy => by
    have := HogAtt.marg0 (hbound x hx) (sub_nonneg.2 hxy)
    rw [show x + (y - x) = y by ring] at this
    linarith
  have h1 : HogAtt.LF G (s1 + s2) ((1 - α) * P.pC + P.cP) zl1 :=
    HogAtt.lvl hG (le_trans hf12 (le_max_left _ _)) hcap hbound
  have h0 : HogAtt.LF G (s1 + s2) P.p1 zb1 := HogAtt.lvl hG (hp12.trans (le_max_right _ _)) hcap hbound
  have h2 : HogAtt.LF G (s1 + s2) P.p2 Zb2 := HogAtt.lvl hG (le_max_right _ _) hcap hbound
  have h20 : Zb2 ≤ zb1 := HogAtt.lvl_anti G hcap hp12
  refine ⟨fun hB hA => ?_, fun hB hA => ?_, fun hB hA => ?_, fun hB hA hAB => ?_⟩
  · have hb : ∀ x y, 0 ≤ x → x ≤ y → G y ≤ G x + P.p2 * (y - x) := fun x y hx hxy => by
      have := hbm x y hx hxy
      rwa [max_eq_right hB.le] at this
    exact HogAtt.case1a hp12 hs1 hs2 hq hB hA h0 hb
  · have hb : ∀ x y, 0 ≤ x → x ≤ y → G y ≤ G x + P.p2 * (y - x) := fun x y hx hxy => by
      have := hbm x y hx hxy
      rwa [max_eq_right hB.le] at this
    have h10 : zl1 ≤ zb1 := HogAtt.lvl_anti G hcap hA
    exact HogAtt.case1b hα0 hpC hp12 hs1 hs2 hq hB hA h1 h0 h10 hb
  · have hb : ∀ x y, 0 ≤ x → x ≤ y → G y ≤ G x + (P.pC + P.cP) * (y - x) :=
      fun x y hx hxy => by
        have := hbm x y hx hxy
        rwa [max_eq_left hB] at this
    exact HogAtt.case2a hp12 hs1 hs2 hq hB hA h0 h2 h20 hb
  · have hb : ∀ x y, 0 ≤ x → x ≤ y → G y ≤ G x + (P.pC + P.cP) * (y - x) :=
      fun x y hx hxy => by
        have := hbm x y hx hxy
        rwa [max_eq_left hB] at this
    have h10 : zl1 ≤ zb1 := HogAtt.lvl_anti G hcap (sub_nonneg.1 hA)
    exact HogAtt.case2b hα0 hpC hp12 hs1 hs2 hq hB hA hAB h1 h0 h2 h10 h20 hb
