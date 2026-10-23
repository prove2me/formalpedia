-- Prove2me | solution 1 for MinEarnings.Threshold.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T10:16:22.0108+00:00
-- url     : https://prove2.me/submissions/1fa60a77-29aa-4ab9-bb13-dd851226098a

import Mathlib
import Definitions.Def_MinEarnings_Threshold_Setting

set_option autoImplicit false

namespace MinEarnings.Threshold.Pf

open MinEarnings.Threshold

lemma cost_lt' {S : ℝ → ℝ} (hSpos : ∀ z, 0 < z → 0 < S z)
    (hSmono : StrictMonoOn S (Set.Ici 0)) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    cost S a < cost S b := by
  unfold cost
  have hb : 0 < b := lt_of_le_of_lt ha hab
  have h1 : S a < S b := hSmono (Set.mem_Ici.2 ha) (Set.mem_Ici.2 hb.le) hab
  have hSb := hSpos b hb
  nlinarith [mul_le_mul_of_nonneg_left h1.le ha, mul_lt_mul_of_pos_right hab hSb]

lemma eq_facts {D S : ℝ → ℝ} {p w z : ℝ} (hSpos : ∀ z, 0 < z → 0 < S z)
    (hz : 0 < z) (he : z = w * util D S p z) (hw : 0 ≤ w) :
    0 < w ∧ cost S z ≤ w * D p ∧ z ≤ w ∧ util D S p z = z / w := by
  have hSz := hSpos z hz
  have hu : util D S p z * S z = min (D p) (S z) := by
    unfold util quantity
    field_simp
  have hu1 : util D S p z ≤ 1 := by
    unfold util quantity
    rw [div_le_one hSz]
    exact min_le_right _ _
  have hwpos : 0 < w := by
    rcases hw.lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at he
      linarith
  refine ⟨hwpos, ?_, ?_, ?_⟩
  · unfold cost
    have h1 : z * S z = w * min (D p) (S z) := by
      calc z * S z = w * util D S p z * S z := by rw [← he]
        _ = w * (util D S p z * S z) := by ring
        _ = w * min (D p) (S z) := by rw [hu]
    rw [h1]
    exact mul_le_mul_of_nonneg_left (min_le_left _ _) hw
  · calc z = w * util D S p z := he
      _ ≤ w * 1 := mul_le_mul_of_nonneg_left hu1 hw
      _ = w := mul_one w
  · rw [eq_div_iff hwpos.ne']
    linear_combination -he

lemma z_le_zStar {D S H : ℝ → ℝ} {pStar wStar p w z : ℝ}
    (hA : Assumptions D S pStar wStar) (hH : IsCostInverse S H)
    (hp : 0 ≤ p) (hpw : w ≤ p) (hw : 0 ≤ w) (hz : 0 < z) (he : z = w * util D S p z) :
    z ≤ zStar D H pStar wStar := by
  obtain ⟨_, hcost, hzw, -⟩ := eq_facts hA.S_pos hz he hw
  have hDp := hA.D_pos p hp
  have hRp : cost S z ≤ revenue D p := by
    unfold revenue
    calc cost S z ≤ w * D p := hcost
      _ ≤ p * D p := mul_le_mul_of_nonneg_right hpw hDp.le
  have hRle : revenue D p ≤ revenue D pStar := by
    rcases le_total p pStar with h | h
    · exact hA.revenue_strictMonoOn.monotoneOn ⟨hp, h⟩ ⟨hA.pStar_nonneg, le_rfl⟩ h
    · exact hA.revenue_strictAntiOn.antitoneOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h) h
  unfold zStar
  split_ifs with hcase
  · by_contra hcon
    push Not at hcon
    have hwS : 0 ≤ wStar := hA.wStar_nonneg
    have h1 : cost S wStar = revenue D wStar := by
      unfold cost revenue
      rw [hA.cross]
    have h2 : cost S wStar < cost S z := cost_lt' hA.S_pos hA.S_strictMonoOn hwS hcon
    have h3 : revenue D p < revenue D wStar :=
      hA.revenue_strictAntiOn (Set.mem_Ici.2 hcase) (Set.mem_Ici.2 (by linarith))
        (by linarith)
    linarith
  · push Not at hcase
    have hp0 : 0 < pStar := lt_of_le_of_lt hA.wStar_nonneg hcase
    have hRpos : 0 < revenue D pStar := mul_pos hp0 (hA.D_pos pStar hp0.le)
    obtain ⟨hHpos, hHc⟩ := hH _ hRpos
    by_contra hcon
    push Not at hcon
    have := cost_lt' hA.S_pos hA.S_strictMonoOn hHpos.le hcon
    linarith

lemma unbounded_of_growth (w : ℕ → ℝ) (c : ℝ) (hc : 1 < c) (T : ℕ) (hT : 0 < w T)
    (hg : ∀ t, T ≤ t → c * w t ≤ w (t + 1)) (B : ℝ) (hB : ∀ t, w t ≤ B) : False := by
  have key : ∀ n : ℕ, c ^ n * w T ≤ w (T + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hg (T + n) (by omega)
      calc c ^ (n + 1) * w T = c * (c ^ n * w T) := by ring
        _ ≤ c * w (T + n) := mul_le_mul_of_nonneg_left ih (by linarith)
        _ ≤ w (T + n + 1) := this
        _ = w (T + (n + 1)) := by rw [Nat.add_assoc]
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (B / w T) hc
  have h1 := key n
  have h2 := hB (T + n)
  rw [div_lt_iff₀ hT] at hn
  linarith

end MinEarnings.Threshold.Pf

open MinEarnings.Threshold in
theorem solution (D S H : ℝ → ℝ) (pStar wStar M : ℝ)
    (hA : Assumptions D S pStar wStar) (hH : IsCostInverse S H)
    (hM : 0 < M) :
    IsStable D S M ↔ M ≤ zStar D H pStar wStar := by
  constructor
  · rintro ⟨p, w, z, hF, hE, hR, ⟨B, hB⟩, hP⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 hP
    have hz_le : ∀ t, T ≤ t → z t ≤ zStar D H pStar wStar := by
      intro t ht
      have hpr := hT t ht
      obtain ⟨hp, hw⟩ := hF t
      obtain ⟨hz, he⟩ := hE t
      have hQ : 0 < quantity D S (p t) (z t) := lt_min (hA.D_pos _ hp) (hA.S_pos _ hz)
      have hpw : w t ≤ p t := by
        unfold profit at hpr
        by_contra h
        push Not at h
        have : (p t - w t) * quantity D S (p t) (z t) < 0 :=
          mul_neg_of_neg_of_pos (by linarith) hQ
        linarith
      exact Pf.z_le_zStar hA hH hp hpw hw hz he
    have hzs_pos : 0 < zStar D H pStar wStar := lt_of_lt_of_le (hE T).1 (hz_le T le_rfl)
    have hg : ∀ t, T ≤ t → (M / zStar D H pStar wStar) * w t ≤ w (t + 1) := by
      intro t ht
      obtain ⟨_, hw⟩ := hF t
      obtain ⟨hz, he⟩ := hE t
      obtain ⟨hwpos, -, -, hu⟩ := Pf.eq_facts hA.S_pos hz he hw
      have h1 := hR t
      rw [hu, div_div_eq_mul_div] at h1
      have h3 : M / zStar D H pStar wStar * w t = M * w t / zStar D H pStar wStar := by ring
      have h4 : M * w t / zStar D H pStar wStar ≤ M * w t / z t := by
        rw [div_le_div_iff₀ hzs_pos hz]
        exact mul_le_mul_of_nonneg_left (hz_le t ht) (mul_pos hM hwpos).le
      linarith
    have hc : 1 < M / zStar D H pStar wStar := by
      rw [one_lt_div hzs_pos]
      exact hcon
    exact Pf.unbounded_of_growth w _ hc T (Pf.eq_facts hA.S_pos (hE T).1 (hE T).2 (hF T).2).1 hg B hB
  · intro hMz
    unfold zStar at hMz
    split_ifs at hMz with hcase
    · have hwpos : 0 < wStar := lt_of_lt_of_le hM hMz
      have hu : util D S wStar wStar = 1 := by
        unfold util quantity
        rw [hA.cross, min_self]
        exact div_self (hA.S_pos _ hwpos).ne'
      refine ⟨fun _ => wStar, fun _ => wStar, fun _ => wStar, ?_, ?_, ?_, ?_, ?_⟩
      · intro t
        exact ⟨hwpos.le, hwpos.le⟩
      · intro t
        refine ⟨hwpos, ?_⟩
        show wStar = wStar * util D S wStar wStar
        rw [hu, mul_one]
      · intro t
        show M / util D S wStar wStar ≤ wStar
        rw [hu, div_one]
        exact hMz
      · exact ⟨wStar, fun _ => le_rfl⟩
      · exact Filter.Eventually.of_forall fun _ => by simp [profit]
    · push Not at hcase
      have hp0 : 0 < pStar := lt_of_le_of_lt hA.wStar_nonneg hcase
      have hDp := hA.D_pos pStar hp0.le
      have hRpos : 0 < revenue D pStar := mul_pos hp0 hDp
      obtain ⟨hh, hhc⟩ := hH _ hRpos
      set zh := H (revenue D pStar) with hzh
      have hc : zh * S zh = pStar * D pStar := hhc
      have hSh := hA.S_pos zh hh
      have hSp : D pStar < S pStar := by
        have h1 : S wStar < S pStar :=
          hA.S_strictMonoOn (Set.mem_Ici.2 hA.wStar_nonneg) (Set.mem_Ici.2 hp0.le) hcase
        have h2 : D pStar < D wStar :=
          hA.D_strictAntiOn (Set.mem_Ici.2 hA.wStar_nonneg) (Set.mem_Ici.2 hp0.le) hcase
        linarith [hA.cross]
      have hge : D pStar ≤ S zh := by
        rcases le_or_gt zh pStar with h1 | h1
        · by_contra hlt
          push Not at hlt
          nlinarith [mul_lt_mul_of_pos_left hlt hh, mul_le_mul_of_nonneg_right h1 hDp.le]
        · have := hA.S_strictMonoOn (Set.mem_Ici.2 hp0.le) (Set.mem_Ici.2 hh.le) h1
          linarith
      have hu : util D S pStar zh = D pStar / S zh := by
        unfold util quantity
        rw [min_eq_left hge]
      refine ⟨fun _ => pStar, fun _ => pStar, fun _ => zh, ?_, ?_, ?_, ?_, ?_⟩
      · intro t
        exact ⟨hp0.le, hp0.le⟩
      · intro t
        refine ⟨hh, ?_⟩
        show zh = pStar * util D S pStar zh
        rw [hu, mul_div_assoc', eq_div_iff hSh.ne']
        linarith
      · intro t
        show M / util D S pStar zh ≤ pStar
        rw [hu, div_div_eq_mul_div, div_le_iff₀ hDp]
        nlinarith [mul_le_mul_of_nonneg_right hMz hSh.le]
      · exact ⟨pStar, fun _ => le_rfl⟩
      · exact Filter.Eventually.of_forall fun _ => by simp [profit]
