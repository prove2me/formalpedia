-- Prove2me | solution 1 for MIBF.Balanced.lemma_4_7
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T02:13:32.768183+00:00
-- url     : https://prove2.me/submissions/b8499b6f-1ad0-442a-8c84-30d716b6afbf

import Mathlib

lemma slope_pos_local {g : ℝ → ℝ} {d z : ℝ} (h : HasDerivAt g d z) (hd : 0 < d) :
    ∃ δ > 0, ∀ t, t ≠ z → |t - z| < δ → 0 < (g t - g z) / (t - z) := by
  have hs := (hasDerivAt_iff_tendsto_slope.1 h).eventually (lt_mem_nhds hd)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hs
  obtain ⟨δ, hδ, hh⟩ := hs
  refine ⟨δ, hδ, fun t ht hlt => ?_⟩
  have := hh (y := t) (by simpa [Real.dist_eq] using hlt) ht
  simpa [slope_def_field] using this

lemma right_neg_deriv_pos_false {g : ℝ → ℝ} {d z c : ℝ} (h : HasDerivAt g d z) (hd : 0 < d)
    (hzc : z < c) (hz : g z = 0) (hneg : ∀ t, z < t → t ≤ c → g t < 0) : False := by
  obtain ⟨δ, hδ, hh⟩ := slope_pos_local h hd
  set t := z + min (δ / 2) ((c - z) / 2) with ht
  have hm : 0 < min (δ / 2) ((c - z) / 2) := lt_min (by linarith) (by linarith)
  have h1 : z < t := by rw [ht]; linarith
  have h2 : t ≤ c := by
    have := min_le_right (δ / 2) ((c - z) / 2); rw [ht]; linarith
  have h3 : |t - z| < δ := by
    have := min_le_left (δ / 2) ((c - z) / 2)
    rw [abs_of_pos (by linarith)]; rw [ht]; linarith
  have := hh t (ne_of_gt h1) h3
  have h4 := hneg t h1 h2
  rw [hz] at this
  have : 0 < g t - 0 := by
    have hp : 0 < t - z := by linarith
    have := (div_pos_iff_of_pos_right hp).1 this
    exact this
  linarith

lemma left_pos_of_deriv_neg {g : ℝ → ℝ} {d z : ℝ} (h : HasDerivAt g d z) (hd : d < 0)
    (hz : g z = 0) : ∃ δ > 0, ∀ t, z - δ < t → t < z → 0 < g t := by
  have h' : HasDerivAt (fun x => - g x) (-d) z := h.neg
  obtain ⟨δ, hδ, hh⟩ := slope_pos_local h' (by linarith)
  refine ⟨δ, hδ, fun t h1 h2 => ?_⟩
  have := hh t (ne_of_lt h2) (by rw [abs_of_neg (by linarith)]; linarith)
  have hp : t - z < 0 := by linarith
  simp only [hz, neg_zero] at this
  by_contra hcon
  have : (-g t - 0) / (t - z) ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by linarith) hp.le
  linarith

lemma right_nonneg {g : ℝ → ℝ} {w b : ℝ} (hc : ContinuousAt g w) (hb : w < b)
    (h : ∀ t, w < t → t ≤ b → 0 ≤ g t) : 0 ≤ g w := by
  have hev : ∀ᶠ t in nhdsWithin w (Set.Ioi w), 0 ≤ g t :=
    Filter.mem_of_superset (Ioc_mem_nhdsGT hb) (fun t ht => h t ht.1 ht.2)
  exact ge_of_tendsto (hc.tendsto.mono_left nhdsWithin_le_nhds) hev

lemma no_two_nonneg {g g' : ℝ → ℝ} {D : Set ℝ} (hder : ∀ r ∈ D, HasDerivAt g (g' r) r)
    (hfold : ∀ r ∈ D, 0 ≤ g r → g' r ≠ 0) {p q : ℝ} (hpq : p < q)
    (hD : Set.Icc p q ⊆ D) (hnn : ∀ t ∈ Set.Icc p q, 0 ≤ g t) (heq : g p = g q) : False := by
  obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero hpq
    (fun t ht => (hder t (hD ht)).continuousAt.continuousWithinAt) heq
    (fun t ht => hder t (hD ⟨ht.1.le, ht.2.le⟩))
  exact hfold c (hD ⟨hc.1.le, hc.2.le⟩) (hnn c ⟨hc.1.le, hc.2.le⟩) hc0

lemma abstract_unique {g g' : ℝ → ℝ} {D : Set ℝ}
    (hlow : ∀ r ∈ D, ∀ t, 0 < t → t ≤ r → t ∈ D)
    (hder : ∀ r ∈ D, HasDerivAt g (g' r) r) (hfold : ∀ r ∈ D, 0 ≤ g r → g' r ≠ 0)
    (hstart : ∃ ε > 0, ∀ t, 0 < t → t < ε → g t < 0) {r1 r2 : ℝ} (h1 : r1 ∈ D) (h2 : r2 ∈ D)
    (hr1 : 0 < r1) (hlt : r1 < r2) (heq : g r1 = g r2) (hnn : 0 ≤ g r1) : False := by
  have hDI : ∀ t, 0 < t → t ≤ r2 → t ∈ D := fun t ht ht2 => hlow r2 h2 t ht ht2
  have hcont : ContinuousOn g (Set.Ioc 0 r2) := fun t ht =>
    (hder t (hDI t ht.1 ht.2)).continuousAt.continuousWithinAt
  by_cases hall : ∀ t ∈ Set.Icc r1 r2, 0 ≤ g t
  · exact no_two_nonneg hder hfold hlt (fun t ht => hDI t (by linarith [ht.1]) ht.2) hall heq
  push Not at hall
  obtain ⟨c, hc, hcneg⟩ := hall
  have hc1 : r1 < c := lt_of_le_of_ne hc.1 (by rintro rfl; linarith)
  have hc2 : c < r2 := lt_of_le_of_ne hc.2 (by rintro rfl; linarith)
  -- last nonnegative point z before c
  have hclT : IsClosed (Set.Icc r1 c ∩ g ⁻¹' Set.Ici 0) :=
    (hcont.mono (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩ : Set.Icc r1 c ⊆ Set.Ioc 0 r2)).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_Ici
  have hTc : IsCompact (Set.Icc r1 c ∩ g ⁻¹' Set.Ici 0) :=
    isCompact_Icc.of_isClosed_subset hclT Set.inter_subset_left
  have hTne : (Set.Icc r1 c ∩ g ⁻¹' Set.Ici 0).Nonempty :=
    ⟨r1, ⟨le_refl _, hc.1⟩, hnn⟩
  have hzmem := hTc.sSup_mem hTne
  set z := sSup (Set.Icc r1 c ∩ g ⁻¹' Set.Ici 0) with hzdef
  have hz0 : 0 ≤ g z := hzmem.2
  have hzc : z < c := lt_of_le_of_ne hzmem.1.2 (by rintro h; rw [h] at hz0; linarith)
  have hzr1 : r1 ≤ z := hzmem.1.1
  have hneg : ∀ t, z < t → t ≤ c → g t < 0 := by
    intro t h1 h2
    by_contra hcon
    push Not at hcon
    have : t ≤ z := le_csSup hTc.bddAbove ⟨⟨by linarith, h2⟩, hcon⟩
    linarith
  have hzpos : 0 < z := by linarith
  have hzD : z ∈ D := hDI z hzpos (by linarith)
  have hcz : ContinuousAt g z := (hder z hzD).continuousAt
  have hgz : g z = 0 := by
    have := right_nonneg (g := fun x => - g x) hcz.neg hzc (fun t h1 h2 => by have := hneg t h1 h2; simp; linarith)
    simp at this; linarith
  have hd0 : g' z ≠ 0 := hfold z hzD hz0
  have hdneg : g' z < 0 := by
    rcases lt_or_gt_of_ne hd0 with h | h
    · exact h
    · exact (right_neg_deriv_pos_false (hder z hzD) h hzc hgz hneg).elim
  obtain ⟨δ, hδ, hleft⟩ := left_pos_of_deriv_neg (hder z hzD) hdneg hgz
  obtain ⟨ε, hε, hstart'⟩ := hstart
  set z2 := z - min δ z / 2 with hz2
  have hmz : 0 < min δ z := lt_min hδ hzpos
  have hz2a : z - δ < z2 := by have := min_le_left δ z; rw [hz2]; linarith
  have hz2b : z2 < z := by rw [hz2]; linarith
  have hz2c : 0 < z2 := by have := min_le_right δ z; rw [hz2]; linarith
  set t0 := min ε z2 / 2 with ht0
  have hmt : 0 < min ε z2 := lt_min hε hz2c
  have ht0a : 0 < t0 := by rw [ht0]; linarith
  have ht0b : t0 < z2 := by have := min_le_right ε z2; rw [ht0]; linarith
  have ht0c : t0 < ε := by have := min_le_left ε z2; rw [ht0]; linarith
  have hgt0 : g t0 < 0 := hstart' t0 ht0a ht0c
  have hclV : IsClosed (Set.Icc t0 z2 ∩ g ⁻¹' Set.Iic 0) :=
    (hcont.mono (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩ : Set.Icc t0 z2 ⊆ Set.Ioc 0 r2)).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_Iic
  have hVc : IsCompact (Set.Icc t0 z2 ∩ g ⁻¹' Set.Iic 0) :=
    isCompact_Icc.of_isClosed_subset hclV Set.inter_subset_left
  have hVne : (Set.Icc t0 z2 ∩ g ⁻¹' Set.Iic 0).Nonempty := ⟨t0, ⟨le_refl _, ht0b.le⟩, hgt0.le⟩
  have hwmem := hVc.sSup_mem hVne
  set w := sSup (Set.Icc t0 z2 ∩ g ⁻¹' Set.Iic 0) with hwdef
  have hw0 : g w ≤ 0 := hwmem.2
  have hgz2 : 0 < g z2 := hleft z2 hz2a hz2b
  have hwz2 : w < z2 := lt_of_le_of_ne hwmem.1.2 (by rintro h; rw [h] at hw0; linarith)
  have hwt0 : t0 ≤ w := hwmem.1.1
  have hpos : ∀ t, w < t → t ≤ z2 → 0 < g t := by
    intro t h1 h2
    by_contra hcon
    push Not at hcon
    have : t ≤ w := le_csSup hVc.bddAbove ⟨⟨by linarith, h2⟩, hcon⟩
    linarith
  have hwD : w ∈ D := hDI w (by linarith) (by linarith)
  have hgw : 0 ≤ g w := right_nonneg (hder w hwD).continuousAt hwz2 (fun t h1 h2 => (hpos t h1 h2).le)
  have hgw0 : g w = 0 := le_antisymm hw0 hgw
  refine no_two_nonneg hder hfold (p := w) (q := z) (by linarith) (fun t ht => hDI t (by linarith [ht.1]) (by linarith [ht.2])) ?_ (by rw [hgw0, hgz])
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h | h
  · rw [← h]; exact hgw
  rcases le_or_gt t z2 with h' | h'
  · exact (hpos t h h').le
  rcases eq_or_lt_of_le ht.2 with h'' | h''
  · rw [h'']; exact hgz.ge
  · exact (hleft t (by linarith) h'').le

noncomputable def Yc (α β K1 r : ℝ) : ℝ :=
  Real.exp ((K1 - (1 - r) ^ 2 / (2 * r) - α * Real.log r) / (α + β))

noncomputable def gc (α β K1 r : ℝ) : ℝ :=
  α * Real.log (1 - r * Yc α β K1 r) + β * Real.log (1 - Yc α β K1 r)
    + Yc α β K1 r ^ 2 * (1 - r) ^ 2 / (2 * (1 - r * Yc α β K1 r) * (1 - Yc α β K1 r))

/-- derivative of `gc`, written via `s = (1-y)/(1-r y)`. -/
noncomputable def gdc (α β K1 r : ℝ) : ℝ :=
  let y := Yc α β K1 r
  let s := (1 - y) / (1 - r * y)
  (1 - s) * (1 - r * s) *
    ((1 - r ^ 2) * (1 - s ^ 2) - 2 * (1 + r * s) * (α * r + β * s) + 4 * α * β * r * s)
    / (4 * (α + β) * r ^ 2 * s ^ 2 * (1 - r))

def Dom (α β K1 : ℝ) : Set ℝ := {r | 0 < r ∧ r < 1 ∧ Yc α β K1 r < 1}


lemma log_le_two_div {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1) :
    Real.log r ≤ 2 * (r - 1) / (r + 1) := by
  have hd : ∀ t ∈ Set.Ioi (0:ℝ), HasDerivAt (fun t => 2 * (t - 1) / (t + 1) - Real.log t)
      (4 / (t + 1) ^ 2 - 1 / t) t := by
    intro t ht
    have ht : (0:ℝ) < t := ht
    have h1 : HasDerivAt (fun t : ℝ => 2 * (t - 1) / (t + 1)) (4 / (t + 1) ^ 2) t := by
      have := ((hasDerivAt_id' t).sub_const 1 |>.const_mul 2).div ((hasDerivAt_id' t).add_const 1) (by simp; linarith)
      refine HasDerivAt.congr_deriv this ?_
      field_simp; ring
    exact h1.sub (Real.hasDerivAt_log ht.ne') |>.congr_deriv (by ring)
  have hmono : AntitoneOn (fun t => 2 * (t - 1) / (t + 1) - Real.log t) (Set.Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    · intro t ht; exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht; rw [interior_Ioi] at ht; exact (hd t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ioi] at ht
      have ht : (0:ℝ) < t := ht
      rw [(hd t ht).deriv]
      have : 4 / (t + 1) ^ 2 - 1 / t = -((t - 1) ^ 2 / (t * (t + 1) ^ 2)) := by
        field_simp; ring
      rw [this]
      have : 0 ≤ (t - 1) ^ 2 / (t * (t + 1) ^ 2) := by positivity
      linarith
  have := hmono (Set.mem_Ioi.2 h0) (Set.mem_Ioi.2 one_pos) h1
  simp at this
  linarith

lemma fold_alg {a b r s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hr0 : 0 < r) (hr1 : r < 1)
    (hs0 : 0 < s) (hs1 : s < 1)
    (hR : (1 - r ^ 2) * (1 - s ^ 2) - 2 * (1 + r * s) * (a * r + b * s) + 4 * a * b * r * s = 0)
    (hL1 : 0 ≤ (1 - r ^ 2) * (1 - r * s) - 2 * a * r * (2 + s - r * s) - 2 * b * r * s * (1 + r))
    (hL2 : 0 ≤ (1 - s ^ 2) * (1 - r * s) - 2 * a * r * s * (1 + s) - 2 * b * s * (2 + r - r * s)) :
    False := by
  have hrs : 0 < r * s := mul_pos hr0 hs0
  have hrs1 : r * s < 1 := by nlinarith
  have hPQ : (1 + r * s - 2 * a * r) * (1 + r * s - 2 * b * s) = (r + s) ^ 2 := by nlinarith
  have hPle : 1 + r * s - 2 * a * r ≤ 1 + r * s := by nlinarith
  have hQle : 1 + r * s - 2 * b * s ≤ 1 + r * s := by nlinarith
  have hpos : 0 < (r + s) ^ 2 := by positivity
  have hid : (1 - s) * ((1 - r ^ 2) * (1 - r * s) - 2 * a * r * (2 + s - r * s) - 2 * b * r * s * (1 + r))
      + (1 - r) * ((1 - s ^ 2) * (1 - r * s) - 2 * a * r * s * (1 + s) - 2 * b * s * (2 + r - r * s))
      = 2 * (1 - r * s) * ((1 + r * s - 2 * a * r) + (1 + r * s - 2 * b * s))
        + (-r^3*s^2 + r^3*s - r^2*s^3 + 4*r^2*s^2 + 2*r^2*s - r^2 + r*s^3 + 2*r*s^2 - 2*r*s - r - s^2 - s - 2) := by
    ring
  set P := 1 + r * s - 2 * a * r with hP
  set Q := 1 + r * s - 2 * b * s with hQ
  have hL1' : (1 - r ^ 2) * (1 - r * s) - 2 * a * r * (2 + s - r * s) - 2 * b * r * s * (1 + r)
      = (2 + s - r * s) * P + r * (1 + r) * Q - (1 + s) * (2 * r ^ 2 + r * s + r + 1 - r ^ 2 * s) := by
    rw [hP, hQ]; ring
  have hconst : 0 < (1 + s) * (2 * r ^ 2 + r * s + r + 1 - r ^ 2 * s) := by
    have : 0 < 2 * r ^ 2 + r * s + r + 1 - r ^ 2 * s := by nlinarith
    positivity
  by_cases hPpos : 0 < P
  · have hQpos : 0 < Q := by
      by_contra hQ'; push Not at hQ'
      nlinarith
    have key : (1 + r * s) * (P + Q) ≤ (1 + r * s) ^ 2 + (r + s) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.2 hPle) (sub_nonneg.2 hQle)]
    have hfin : (1 + r * s) * ((1 - s) * ((1 - r ^ 2) * (1 - r * s) - 2 * a * r * (2 + s - r * s) - 2 * b * r * s * (1 + r))
      + (1 - r) * ((1 - s ^ 2) * (1 - r * s) - 2 * a * r * s * (1 + s) - 2 * b * s * (2 + r - r * s)))
      ≤ -((1 - r) * (1 - s) * (1 - r * s) ^ 2 * (r + s)) := by
      rw [hid]
      have h2 : 0 < 1 - r * s := by linarith
      nlinarith [mul_le_mul_of_nonneg_left key (by linarith : (0:ℝ) ≤ 2 * (1 - r * s))]
    have : 0 < (1 - r) * (1 - s) * (1 - r * s) ^ 2 * (r + s) := by
      have : 0 < 1 - r * s := by linarith
      have : 0 < 1 - r := by linarith
      have : 0 < 1 - s := by linarith
      positivity
    have h3 : 0 ≤ (1 + r * s) * ((1 - s) * ((1 - r ^ 2) * (1 - r * s) - 2 * a * r * (2 + s - r * s) - 2 * b * r * s * (1 + r))
      + (1 - r) * ((1 - s ^ 2) * (1 - r * s) - 2 * a * r * s * (1 + s) - 2 * b * s * (2 + r - r * s))) := by
      have h4 : 0 ≤ (1 - s) * ((1 - r ^ 2) * (1 - r * s) - 2 * a * r * (2 + s - r * s) - 2 * b * r * s * (1 + r))
      + (1 - r) * ((1 - s ^ 2) * (1 - r * s) - 2 * a * r * s * (1 + s) - 2 * b * s * (2 + r - r * s)) := by
        have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - s) hL1
        have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - r) hL2
        linarith
      positivity
    linarith
  · have hPneg : P < 0 := by
      rcases lt_or_eq_of_le (not_lt.1 hPpos) with h | h
      · exact h
      · rw [h] at hPQ; nlinarith
    have hQneg : Q < 0 := by
      by_contra hQ'; push Not at hQ'
      nlinarith
    rw [hL1'] at hL1
    nlinarith [mul_pos hr0 (by linarith : (0:ℝ) < 1 + r)]

lemma L_of_F {a b r s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hr0 : 0 < r) (hr1 : r < 1)
    (hs0 : 0 < s) (hs1 : s < 1)
    (hF : 0 ≤ (1 - r) ^ 2 / (2 * r) + a * Real.log r + (a + b) * Real.log ((1 - s) / (1 - r * s))) :
    0 ≤ (1 - r ^ 2) * (1 - r * s) - 2 * a * r * (2 + s - r * s) - 2 * b * r * s * (1 + r) := by
  have hrs : r * s < 1 := by nlinarith
  have h1 : 0 < 1 - r * s := by linarith
  have hy : 0 < (1 - s) / (1 - r * s) := div_pos (by linarith) h1
  have hl1 := log_le_two_div hr0 hr1.le
  have hl2 := Real.log_le_sub_one_of_pos hy
  have h1' : 1 - r * s ≠ 0 := h1.ne'
  have hy1 : (1 - s) / (1 - r * s) - 1 = -(s * (1 - r) / (1 - r * s)) := by
    have : (1 - s) / (1 - r * s) = 1 - s * (1 - r) / (1 - r * s) := by
      rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq h1']; ring
    linarith
  rw [hy1] at hl2
  have hle : (1 - r) ^ 2 / (2 * r) + a * Real.log r + (a + b) * Real.log ((1 - s) / (1 - r * s))
      ≤ (1 - r) ^ 2 / (2 * r) + a * (2 * (r - 1) / (r + 1)) + (a + b) * (-(s * (1 - r) / (1 - r * s))) := by
    have := mul_le_mul_of_nonneg_left hl1 ha
    have := mul_le_mul_of_nonneg_left hl2 (by linarith : 0 ≤ a + b)
    linarith
  have e1 : (1 - r) ^ 2 / (2 * r) + a * (2 * (r - 1) / (r + 1)) + (a + b) * (-(s * (1 - r) / (1 - r * s)))
      = (1 - r) / (2 * r * (1 + r) * (1 - r * s)) *
        ((1 - r ^ 2) * (1 - r * s) - 2 * a * r * (2 + s - r * s) - 2 * b * r * s * (1 + r)) := by
    have : r + 1 ≠ 0 := by linarith
    have : r ≠ 0 := hr0.ne'
    have : 1 + r ≠ 0 := by linarith
    field_simp
    ring
  have hc : 0 < (1 - r) / (2 * r * (1 + r) * (1 - r * s)) := by
    have : 0 < 1 - r := by linarith
    positivity
  have h0 := hF.trans hle
  rw [e1] at h0
  exact (mul_nonneg_iff_of_pos_left hc).1 h0

lemma fold_rs {a b r s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hr0 : 0 < r) (hr1 : r < 1)
    (hs0 : 0 < s) (hs1 : s < 1)
    (hF1 : 0 ≤ (1 - r) ^ 2 / (2 * r) + a * Real.log r + (a + b) * Real.log ((1 - s) / (1 - r * s)))
    (hF0 : 0 ≤ (1 - s) ^ 2 / (2 * s) + b * Real.log s + (a + b) * Real.log ((1 - r) / (1 - r * s))) :
    (1 - r ^ 2) * (1 - s ^ 2) - 2 * (1 + r * s) * (a * r + b * s) + 4 * a * b * r * s ≠ 0 := by
  intro hR
  have hL1 := L_of_F ha hb hr0 hr1 hs0 hs1 hF1
  have hL2 := L_of_F (a := b) (b := a) (r := s) (s := r) hb ha hs0 hs1 hr0 hr1
    (by rw [mul_comm s r, add_comm b a]; exact hF0)
  refine fold_alg ha hb hr0 hr1 hs0 hs1 hR hL1 ?_
  convert hL2 using 1
  ring

lemma G0_deriv {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => (1 - x) ^ 2 / (2 * x)) ((x ^ 2 - 1) / (2 * x ^ 2)) x := by
  have hn : HasDerivAt (fun x : ℝ => (1 - x) ^ 2) (-(2 * (1 - x))) x := by
    have := (hasDerivAt_pow 2 (1 - x)).comp x ((hasDerivAt_id' x).const_sub 1)
    refine HasDerivAt.congr_deriv this ?_
    simp
  have hd : HasDerivAt (fun x : ℝ => 2 * x) 2 x := by
    simpa using (hasDerivAt_id' x).const_mul 2
  refine HasDerivAt.congr_deriv (hn.div hd (by positivity)) ?_
  field_simp; ring

lemma Yc_lt_one_iff {α β K1 t : ℝ} (hαβ : 0 < α + β) :
    Yc α β K1 t < 1 ↔ K1 < (1 - t) ^ 2 / (2 * t) + α * Real.log t := by
  unfold Yc
  rw [← Real.exp_zero, Real.exp_lt_exp, div_lt_iff₀ hαβ]
  constructor <;> intro h <;> linarith

lemma Dom_lower {α β K1 : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : 0 < α + β) (hK1 : 0 ≤ K1) :
    ∀ r ∈ Dom α β K1, ∀ t, 0 < t → t ≤ r → t ∈ Dom α β K1 := by
  rintro r ⟨hr0, hr1, hY⟩ t ht htr
  refine ⟨ht, by linarith, ?_⟩
  rw [Yc_lt_one_iff hαβ] at hY ⊢
  have hlog := log_le_two_div hr0 hr1.le
  have hq : r ^ 2 + 2 * α * r < 1 := by
    have h1 : α * Real.log r ≤ α * (2 * (r - 1) / (r + 1)) := mul_le_mul_of_nonneg_left hlog hα
    have h2 : 0 < (1 - r) ^ 2 / (2 * r) + α * (2 * (r - 1) / (r + 1)) := by linarith
    have e : (1 - r) ^ 2 / (2 * r) + α * (2 * (r - 1) / (r + 1))
        = (1 - r) * ((1 - r ^ 2 - 4 * α * r)) / (2 * r * (r + 1)) := by
      have : r + 1 ≠ 0 := by linarith
      have : r ≠ 0 := hr0.ne'
      field_simp; ring
    rw [e] at h2
    have h3 : 0 < (1 - r) * (1 - r ^ 2 - 4 * α * r) := by
      have : 0 < 2 * r * (r + 1) := by positivity
      exact (div_pos_iff_of_pos_right this).1 h2
    have h4 : 0 < 1 - r ^ 2 - 4 * α * r := (mul_pos_iff_of_pos_left (by linarith)).1 h3
    nlinarith
  have hd : ∀ x ∈ Set.Ioi (0:ℝ), HasDerivAt (fun x => (1 - x) ^ 2 / (2 * x) + α * Real.log x)
      ((x ^ 2 + 2 * α * x - 1) / (2 * x ^ 2)) x := by
    intro x hx
    have hx : (0:ℝ) < x := hx
    have h1 := G0_deriv hx
    refine (h1.add ((Real.hasDerivAt_log hx.ne').const_mul α)).congr_deriv ?_
    field_simp; ring
  have hmono : AntitoneOn (fun x => (1 - x) ^ 2 / (2 * x) + α * Real.log x) (Set.Ioc 0 r) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioc 0 r)
    · intro x hx; exact (hd x hx.1).continuousAt.continuousWithinAt
    · intro x hx; rw [interior_Ioc] at hx
      exact (hd x hx.1).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ioc] at hx
      rw [(hd x hx.1).deriv]
      have hx0 : (0:ℝ) < x := hx.1
      apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      nlinarith [hx.2]
  have := hmono ⟨ht, htr⟩ ⟨hr0, le_refl r⟩ htr
  simp only at this
  linarith

lemma Yc_deriv {α β K1 r : ℝ} (hαβ : 0 < α + β) (hr : 0 < r) :
    HasDerivAt (Yc α β K1) (Yc α β K1 r * ((1 - r ^ 2 - 2 * α * r) / (2 * r ^ 2 * (α + β)))) r := by
  have h1 := G0_deriv hr
  have h2 : HasDerivAt (fun x : ℝ => (K1 - (1 - x) ^ 2 / (2 * x) - α * Real.log x) / (α + β))
      ((0 - (r ^ 2 - 1) / (2 * r ^ 2) - α * r⁻¹) / (α + β)) r :=
    (((hasDerivAt_const r K1).sub h1).sub ((Real.hasDerivAt_log hr.ne').const_mul α)).div_const (α + β)
  have h3 := h2.exp
  have : r ≠ 0 := hr.ne'
  have : α + β ≠ 0 := hαβ.ne'
  unfold Yc
  refine HasDerivAt.congr_deriv h3 ?_
  congr 1
  field_simp
  ring

set_option maxRecDepth 100000 in
lemma gc_deriv {α β K1 : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : 0 < α + β) (hK1 : 0 ≤ K1) :
    ∀ r ∈ Dom α β K1, HasDerivAt (gc α β K1) (gdc α β K1 r) r := by
  rintro r ⟨hr0, hr1, hy1⟩
  have hY := Yc_deriv (K1 := K1) hαβ hr0
  set Y := Yc α β K1 r with hYdef
  set Y' := Y * ((1 - r ^ 2 - 2 * α * r) / (2 * r ^ 2 * (α + β))) with hY'
  have hYpos : 0 < Y := Real.exp_pos _
  have hA0 : 0 < 1 - r * Y := by nlinarith
  have hB0 : 0 < 1 - Y := by linarith
  have hA : HasDerivAt (fun x => 1 - x * Yc α β K1 x) (-(Y + r * Y')) r := by
    have := ((hasDerivAt_id' r).mul hY).const_sub 1
    refine HasDerivAt.congr_deriv this ?_
    simp <;> rfl
  have hB : HasDerivAt (fun x => 1 - Yc α β K1 x) (-Y') r := by
    simpa using hY.const_sub 1
  have hS : HasDerivAt (fun x : ℝ => (1 - x) ^ 2) (-(2 * (1 - r))) r := by
    have := (hasDerivAt_pow 2 (1 - r)).comp r ((hasDerivAt_id' r).const_sub 1)
    refine HasDerivAt.congr_deriv this ?_
    simp
  have hP : HasDerivAt (fun x => Yc α β K1 x ^ 2) (2 * Y * Y') r := by
    have := (hasDerivAt_pow 2 Y).comp r hY
    refine HasDerivAt.congr_deriv this ?_
    simp
  have hN := hP.mul hS
  have hD := ((hA.const_mul 2).mul hB)
  have n1 : 1 - r * Y ≠ 0 := hA0.ne'
  have hQ := hN.div hD (by
    exact mul_ne_zero (mul_ne_zero two_ne_zero n1) hB0.ne')
  have hL1 := (hA.log hA0.ne').const_mul α
  have hL2 := (hB.log hB0.ne').const_mul β
  have hT := (hL1.add hL2).add hQ
  refine HasDerivAt.congr_deriv hT ?_
  have n2 : 1 - Y * r ≠ 0 := by rw [mul_comm]; exact hA0.ne'
  have n3 : 1 - Y ≠ 0 := hB0.ne'
  have n4 : r ≠ 0 := hr0.ne'
  have n5 : α + β ≠ 0 := hαβ.ne'
  have n6 : 1 - r ≠ 0 := by linarith
  unfold gdc
  dsimp only
  simp only [Pi.mul_apply, Pi.div_apply]
  rw [← hYdef, hY']
  clear_value Y' Y
  field_simp
  ring

lemma gc_fold {α β K1 : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : 0 < α + β) (hK1 : 0 ≤ K1) :
    ∀ r ∈ Dom α β K1, 0 ≤ gc α β K1 r → gdc α β K1 r ≠ 0 := by
  rintro r ⟨hr0, hr1, hy1⟩ hg
  set y := Yc α β K1 r with hy
  have hypos : 0 < y := Real.exp_pos _
  have hry : 0 < 1 - r * y := by nlinarith
  set s := (1 - y) / (1 - r * y) with hs
  have hs0 : 0 < s := div_pos (by linarith) hry
  have hs1 : s < 1 := by rw [hs, div_lt_one hry]; nlinarith
  have hrs : 0 < 1 - r * s := by nlinarith
  have n1 : 1 - r * y ≠ 0 := hry.ne'
  have n2 : 1 - y * r ≠ 0 := by rw [mul_comm]; exact hry.ne'
  have n3 : 1 - r * s ≠ 0 := hrs.ne'
  have n4 : 1 - s * r ≠ 0 := by rw [mul_comm]; exact hrs.ne'
  have n5 : 1 - r ≠ 0 := by linarith
  have n6 : r ≠ 0 := hr0.ne'
  have n7 : s ≠ 0 := hs0.ne'
  have hyeq : y = (1 - s) / (1 - r * s) := by
    rw [hs]
    have h1 : 1 - r * ((1 - y) / (1 - r * y)) = (1 - r) / (1 - r * y) := by
      field_simp; ring
    have h2 : 1 - (1 - y) / (1 - r * y) = y * (1 - r) / (1 - r * y) := by
      field_simp; ring
    rw [h1, h2]
    have : 1 - r ≠ 0 := by linarith
    field_simp
  -- F1
  have hlogy : Real.log y = (K1 - (1 - r) ^ 2 / (2 * r) - α * Real.log r) / (α + β) := by
    rw [hy]; unfold Yc; rw [Real.log_exp]
  have hF1 : 0 ≤ (1 - r) ^ 2 / (2 * r) + α * Real.log r + (α + β) * Real.log ((1 - s) / (1 - r * s)) := by
    rw [← hyeq, hlogy]
    have : (α + β) * ((K1 - (1 - r) ^ 2 / (2 * r) - α * Real.log r) / (α + β))
        = K1 - (1 - r) ^ 2 / (2 * r) - α * Real.log r := by field_simp
    rw [this]; linarith
  have hu : 1 - r * y = (1 - r) / (1 - r * s) := by
    rw [hyeq]; field_simp; ring
  have hv : 1 - y = s * ((1 - r) / (1 - r * s)) := by
    rw [← hu, hs]; field_simp
  have hF0 : 0 ≤ (1 - s) ^ 2 / (2 * s) + β * Real.log s + (α + β) * Real.log ((1 - r) / (1 - r * s)) := by
    have e : gc α β K1 r = (1 - s) ^ 2 / (2 * s) + β * Real.log s + (α + β) * Real.log ((1 - r) / (1 - r * s)) := by
      have hne : (1 - r) / (1 - r * s) ≠ 0 := by
        have : 0 < 1 - r := by linarith
        positivity
      unfold gc
      rw [← hy, hu, hv, Real.log_mul hs0.ne' hne]
      have : 1 - r ≠ 0 := by linarith
      have h3 : y ^ 2 * (1 - r) ^ 2 / (2 * ((1 - r) / (1 - r * s)) * (s * ((1 - r) / (1 - r * s))))
          = (1 - s) ^ 2 / (2 * s) := by
        rw [hyeq]; field_simp
      rw [h3]; ring
    rw [← e]; exact hg
  have hR := fold_rs hα hβ hr0 hr1 hs0 hs1 hF1 hF0
  show (1 - s) * (1 - r * s) *
    ((1 - r ^ 2) * (1 - s ^ 2) - 2 * (1 + r * s) * (α * r + β * s) + 4 * α * β * r * s)
    / (4 * (α + β) * r ^ 2 * s ^ 2 * (1 - r)) ≠ 0
  have h1s : 1 - s ≠ 0 := by linarith
  have hab : α + β ≠ 0 := hαβ.ne'
  refine div_ne_zero (mul_ne_zero (mul_ne_zero h1s n3) hR) ?_
  positivity

lemma Yc_small {α β K1 t : ℝ} (hα : 0 ≤ α) (hαβ : 0 < α + β) (hK1 : 0 ≤ K1) (ht : 0 < t)
    (ht4 : t ≤ 1 / 4) (htM : 16 * (K1 + α * Real.log (8 * α + 8) + 1) * t ≤ 1) :
    Yc α β K1 t ≤ 512 * (α + β) ^ 2 * t ^ 2 := by
  have hC : 0 < Real.log (8 * α + 8) := Real.log_pos (by linarith)
  have hG : 1 / (4 * t) ≤ (1 - t) ^ 2 / (2 * t) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h : 1 / 2 ≤ (1 - t) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right h (by linarith : (0:ℝ) ≤ 4 * t)]
  have hε : 0 < 1 / (8 * α + 8) := by positivity
  have hlog1 := Real.log_le_sub_one_of_pos (div_pos hε ht)
  rw [Real.log_div hε.ne' ht.ne', one_div, Real.log_inv] at hlog1
  simp only [← one_div] at hlog1
  have hε2 : α * (1 / (8 * α + 8) / t) ≤ 1 / (8 * t) := by
    have : α * (1 / (8 * α + 8)) ≤ 1 / 8 := by
      rw [← mul_div_assoc, mul_one, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    calc α * (1 / (8 * α + 8) / t) = α * (1 / (8 * α + 8)) / t := by ring
      _ ≤ 1 / 8 / t := by gcongr
      _ = 1 / (8 * t) := by field_simp
  have hnum : K1 - (1 - t) ^ 2 / (2 * t) - α * Real.log t ≤ -(1 / (16 * t)) := by
    have h1 : -Real.log t ≤ 1 / (8 * α + 8) / t - 1 + Real.log (8 * α + 8) := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hα
    have h3 : 16 * (K1 + α * Real.log (8 * α + 8) + 1) ≤ 1 / t := by
      rw [le_div_iff₀ ht]; exact htM
    have h4 : 1 / (16 * t) = 1 / t / 16 := by field_simp
    have h5 : 1 / (4 * t) = 1 / t / 4 := by field_simp
    have h6 : 1 / (8 * t) = 1 / t / 8 := by field_simp
    nlinarith
  set m := α + β with hm
  have hmpos : 0 < m := hαβ
  have hw : 0 < 1 / (16 * m * t) := by positivity
  have hexp : Yc α β K1 t ≤ Real.exp (-(1 / (16 * m * t))) := by
    unfold Yc
    apply Real.exp_le_exp.2
    rw [div_le_iff₀ hmpos]
    have : -(1 / (16 * m * t)) * m = -(1 / (16 * t)) := by field_simp
    rw [this]; exact hnum
  refine hexp.trans ?_
  set w := 1 / (16 * m * t) with hwdef
  have hq := Real.quadratic_le_exp_of_nonneg hw.le
  have hpos : 0 < Real.exp w := Real.exp_pos _
  rw [Real.exp_neg]
  have hw2 : w ^ 2 / 2 ≤ Real.exp w := by nlinarith
  have : (Real.exp w)⁻¹ ≤ (w ^ 2 / 2)⁻¹ := inv_anti₀ (by positivity) hw2
  refine this.trans (le_of_eq ?_)
  rw [hwdef]; field_simp; ring

lemma gc_start {α β K1 : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : 0 < α + β) (hK1 : 0 ≤ K1) :
    ∃ ε > 0, ∀ t, 0 < t → t < ε → gc α β K1 t < 0 := by
  have hC : 0 < Real.log (8 * α + 8) := Real.log_pos (by linarith)
  set M := K1 + α * Real.log (8 * α + 8) + 1 with hM
  have hMpos : 0 < M := by
    have : 0 ≤ α * Real.log (8 * α + 8) := mul_nonneg hα hC.le
    rw [hM]; linarith
  refine ⟨min (1 / 4) (min (1 / (16 * M)) (1 / (2048 * (α + β)))), by positivity, ?_⟩
  intro t ht0 htε
  have ht4 : t ≤ 1 / 4 := (lt_of_lt_of_le htε (min_le_left _ _)).le
  have htM' : t ≤ 1 / (16 * M) :=
    (lt_of_lt_of_le htε ((min_le_right _ _).trans (min_le_left _ _))).le
  have htm' : t ≤ 1 / (2048 * (α + β)) :=
    (lt_of_lt_of_le htε ((min_le_right _ _).trans (min_le_right _ _))).le
  have htM : 16 * M * t ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at htM'; linarith
  have htm : 2048 * (α + β) * t ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at htm'; linarith
  have hY := Yc_small hα hαβ hK1 ht0 ht4 htM
  set Y := Yc α β K1 t with hYdef
  have hYpos : 0 < Y := Real.exp_pos _
  set m := α + β with hmdef
  have hmpos : 0 < m := hαβ
  have hY4 : Y ≤ m * t / 4 := by
    have : 512 * m ^ 2 * t ^ 2 ≤ m * t / 4 := by
      have h1 : 0 < m * t := by positivity
      nlinarith
    linarith
  have ht1 : t < 1 := by linarith
  have hmt : 0 < m * t := by positivity
  have hYs : Y < 1 / 4 := by nlinarith
  have hA : 0 < 1 - t * Y := by nlinarith
  have hB : 0 < 1 - Y := by linarith
  have l1 : Real.log (1 - t * Y) ≤ -(t * Y) := by
    have := Real.log_le_sub_one_of_pos hA; linarith
  have l2 : Real.log (1 - Y) ≤ -Y := by
    have := Real.log_le_sub_one_of_pos hB; linarith
  have h3 : Y ^ 2 * (1 - t) ^ 2 / (2 * (1 - t * Y) * (1 - Y)) ≤ Y ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : 1 ≤ 2 * (1 - t * Y) * (1 - Y) := by nlinarith
    have h2 : (1 - t) ^ 2 ≤ 1 := by nlinarith
    have : 0 ≤ Y ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 this, mul_le_mul_of_nonneg_left h1 this]
  unfold gc
  rw [← hYdef]
  have e1 := mul_le_mul_of_nonneg_left l1 hα
  have e2 := mul_le_mul_of_nonneg_left l2 hβ
  have hmab : m = α + β := hmdef
  have : α * (-(t * Y)) + β * (-Y) + Y ^ 2 < 0 := by
    have : Y * (α * t + β) ≥ Y * (m * t) := by
      apply mul_le_mul_of_nonneg_left _ hYpos.le
      rw [hmab]; nlinarith
    nlinarith
  linarith

lemma sol_param {α β K1 x y : ℝ} (hαβ : 0 < α + β) (hx : 0 < x) (hxy : x < y) (hy : y < 1)
    (h1 : α * Real.log x + β * Real.log y + (x - y) ^ 2 / (2 * x * y) = K1) :
    y = Yc α β K1 (x / y) := by
  have hy0 : 0 < y := hx.trans hxy
  have hr : 0 < x / y := div_pos hx hy0
  have hlog : Real.log (x / y) = Real.log x - Real.log y := Real.log_div hx.ne' hy0.ne'
  have hq : (1 - x / y) ^ 2 / (2 * (x / y)) = (x - y) ^ 2 / (2 * x * y) := by
    field_simp; ring
  unfold Yc
  rw [hq, hlog]
  conv_lhs => rw [← Real.exp_log hy0]
  congr 1
  rw [eq_div_iff hαβ.ne']
  linarith

lemma sol_g {α β K1 K0 x y : ℝ} (hαβ : 0 < α + β) (hx : 0 < x) (hxy : x < y) (hy : y < 1)
    (h1 : α * Real.log x + β * Real.log y + (x - y) ^ 2 / (2 * x * y) = K1)
    (h0 : α * Real.log (1 - x) + β * Real.log (1 - y)
        + (x - y) ^ 2 / (2 * (1 - x) * (1 - y)) = K0) :
    gc α β K1 (x / y) = K0 := by
  have hy0 : 0 < y := hx.trans hxy
  have hY := sol_param hαβ hx hxy hy h1
  have hxe : x / y * y = x := by field_simp
  unfold gc
  rw [← hY, hxe, ← h0]
  congr 1
  have : 1 - y ≠ 0 := by linarith
  have : 1 - x ≠ 0 := by linarith
  field_simp
  ring

theorem solution (α β K0 K1 : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : 0 < α + β)
    (hK0 : 0 ≤ K0) (hK1 : 0 ≤ K1) :
    Set.Subsingleton {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < 1 ∧
      α * Real.log p.1 + β * Real.log p.2 + (p.1 - p.2) ^ 2 / (2 * p.1 * p.2) = K1 ∧
      α * Real.log (1 - p.1) + β * Real.log (1 - p.2)
        + (p.1 - p.2) ^ 2 / (2 * (1 - p.1) * (1 - p.2)) = K0} := by
  rintro ⟨x1, y1⟩ ⟨h1x, h1xy, h1y, h1a, h1b⟩ ⟨x2, y2⟩ ⟨h2x, h2xy, h2y, h2a, h2b⟩
  simp only at *
  have y10 : 0 < y1 := h1x.trans h1xy
  have y20 : 0 < y2 := h2x.trans h2xy
  have hY1 := sol_param hαβ h1x h1xy h1y h1a
  have hY2 := sol_param hαβ h2x h2xy h2y h2a
  have hg1 := sol_g hαβ h1x h1xy h1y h1a h1b
  have hg2 := sol_g hαβ h2x h2xy h2y h2a h2b
  have hD1 : x1 / y1 ∈ Dom α β K1 := ⟨div_pos h1x y10, (div_lt_one y10).2 h1xy, by rw [← hY1]; exact h1y⟩
  have hD2 : x2 / y2 ∈ Dom α β K1 := ⟨div_pos h2x y20, (div_lt_one y20).2 h2xy, by rw [← hY2]; exact h2y⟩
  have key : x1 / y1 = x2 / y2 := by
    by_contra hne
    have hab : ∀ {r1 r2 : ℝ}, r1 ∈ Dom α β K1 → r2 ∈ Dom α β K1 → 0 < r1 → r1 < r2 →
        gc α β K1 r1 = gc α β K1 r2 → 0 ≤ gc α β K1 r1 → False :=
      fun a b c d e f => abstract_unique (g := gc α β K1) (g' := gdc α β K1) (D := Dom α β K1)
        (Dom_lower hα hβ hαβ hK1) (gc_deriv hα hβ hαβ hK1) (gc_fold hα hβ hαβ hK1)
        (gc_start hα hβ hαβ hK1) a b c d e f
    rcases lt_or_gt_of_ne hne with h | h
    · exact hab hD1 hD2 hD1.1 h (hg1.trans hg2.symm) (by rw [hg1]; exact hK0)
    · exact hab hD2 hD1 hD2.1 h (hg2.trans hg1.symm) (by rw [hg2]; exact hK0)
  have hyy : y1 = y2 := by rw [hY1, hY2, key]
  have hxx : x1 = x2 := by
    have := key; rw [hyy] at this
    field_simp at this; exact this
  rw [hxx, hyy]
