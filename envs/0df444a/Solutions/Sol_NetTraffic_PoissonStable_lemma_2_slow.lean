-- Prove2me | solution 1 for NetTraffic.PoissonStable.lemma_2_slow
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T00:59:36.247393+00:00
-- url     : https://prove2.me/submissions/7026d8d0-d1d3-4b23-8d5d-f09ca9364560

import Mathlib
import Definitions.Def_NetTraffic_PoissonStable_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open NetTraffic.PoissonStable

namespace Sol_l2slow

lemma Fbar_anti (Fon : Measure ℝ) [IsFiniteMeasure Fon] : Antitone (Fbar Fon) := by
  intro x y hxy
  unfold Fbar
  exact measureReal_mono (Set.Ioi_subset_Ioi hxy)

lemma Fbar_nonneg (Fon : Measure ℝ) (x : ℝ) : 0 ≤ Fbar Fon x := measureReal_nonneg

lemma Fbar_le_one (Fon : Measure ℝ) [IsProbabilityMeasure Fon] (x : ℝ) : Fbar Fon x ≤ 1 :=
  measureReal_le_one

/-- Iterating the doubling bound. -/
lemma iter (Fon : Measure ℝ) [IsFiniteMeasure Fon] {p x0 : ℝ} (hp : 0 ≤ p) (hx0 : 0 < x0)
    (h : ∀ x ≥ x0, Fbar Fon (2 * x) ≤ p * Fbar Fon x) :
    ∀ n : ℕ, ∀ x ≥ x0, Fbar Fon (2 ^ n * x) ≤ p ^ n * Fbar Fon x := by
  intro n
  induction n with
  | zero => intro x _; simp
  | succ n ih =>
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hx0 hx
    have h1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    have h2 : x0 ≤ 2 ^ n * x := le_trans hx (by nlinarith)
    have e : (2 : ℝ) ^ (n + 1) * x = 2 * (2 ^ n * x) := by ring
    rw [e]
    calc Fbar Fon (2 * (2 ^ n * x)) ≤ p * Fbar Fon (2 ^ n * x) := h _ h2
      _ ≤ p * (p ^ n * Fbar Fon x) := mul_le_mul_of_nonneg_left (ih x hx) hp
      _ = p ^ (n + 1) * Fbar Fon x := by ring

/-- Potter-type bound for `g(x) = x F̄(x)`. -/
lemma potter (Fon : Measure ℝ) [IsFiniteMeasure Fon] {p x0 : ℝ} (hp : 0 ≤ p) (hq : 2 * p ≤ 1)
    (hx0 : 0 < x0) (h : ∀ x ≥ x0, Fbar Fon (2 * x) ≤ p * Fbar Fon x) :
    ∀ u ≥ x0, ∀ N : ℕ, ∀ T : ℝ, 2 ^ N * u ≤ T →
      T * Fbar Fon T ≤ 2 * (2 * p) ^ N * (u * Fbar Fon u) := by
  intro u hu N T hT
  have hupos : 0 < u := lt_of_lt_of_le hx0 hu
  have h2N : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
  have hTu : 1 ≤ T / u := by
    rw [le_div_iff₀ hupos]; nlinarith
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hTu (by norm_num : (1 : ℝ) < 2)
  have hn1' : 2 ^ n * u ≤ T := by rwa [le_div_iff₀ hupos] at hn1
  have hn2' : T < 2 ^ (n + 1) * u := by rwa [div_lt_iff₀ hupos] at hn2
  have hNn : N ≤ n := by
    have : (2 : ℝ) ^ N < 2 ^ (n + 1) := by
      have : (2 : ℝ) ^ N ≤ T / u := by rw [le_div_iff₀ hupos]; exact hT
      linarith
    have := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 this
    omega
  have hTpos : 0 < T := by nlinarith
  have hit := iter Fon hp hx0 h n u hu
  have hF0 := Fbar_nonneg Fon u
  have hFT : Fbar Fon T ≤ Fbar Fon (2 ^ n * u) := Fbar_anti Fon hn1'
  have hpn : (2 * p) ^ n ≤ (2 * p) ^ N :=
    pow_le_pow_of_le_one (by linarith) hq hNn
  calc T * Fbar Fon T ≤ T * (p ^ n * Fbar Fon u) :=
        mul_le_mul_of_nonneg_left (le_trans hFT hit) hTpos.le
    _ ≤ (2 ^ (n + 1) * u) * (p ^ n * Fbar Fon u) :=
        mul_le_mul_of_nonneg_right hn2'.le (mul_nonneg (pow_nonneg hp _) hF0)
    _ = 2 * (2 * p) ^ n * (u * Fbar Fon u) := by rw [mul_pow]; ring
    _ ≤ 2 * (2 * p) ^ N * (u * Fbar Fon u) := by
        have : 0 ≤ u * Fbar Fon u := mul_nonneg hupos.le hF0
        nlinarith

end Sol_l2slow

open Sol_l2slow in
theorem solution
    {Fon : Measure ℝ} [IsProbabilityMeasure Fon] {α : ℝ} (hF : HeavyTail Fon α)
    {lam : ℝ → ℝ} (hlam : ∀ T, 0 < lam T) (hmono : Monotone lam)
    (hC1 : Condition1 Fon lam) :
    Tendsto (fun T => lam T * T ^ 2 * Fbar Fon T / b Fon (lam T * T)) atTop (𝓝 0) := by
  -- constants
  set A2 : ℝ := (2 : ℝ) ^ α with hA2def
  have hA2 : 2 < A2 := by
    have := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hF.one_lt
    simpa [hA2def] using this
  have hA2pos : 0 < A2 := by linarith
  set r : ℝ := (2 + A2) / 4 with hr
  have hr1 : 1 < r := by rw [hr]; linarith
  set p : ℝ := r / A2 with hp
  have hp0 : 0 ≤ p := div_nonneg (by linarith) hA2pos.le
  have hq1 : 2 * p < 1 := by
    rw [hp, hr, mul_div_assoc', div_lt_one hA2pos]; linarith
  -- the doubling bound
  set L : ℝ → ℝ := fun x => x ^ α * Fbar Fon x with hL
  have hSV := hF.slowlyVarying
  have hev : ∀ᶠ x in atTop, 0 < L x ∧ L (2 * x) / L x < r ∧ 0 < x :=
    hSV.1.and (((hSV.2 2 two_pos).eventually (gt_mem_nhds hr1)).and (eventually_gt_atTop 0))
  obtain ⟨a, ha⟩ := eventually_atTop.1 hev
  set x0 : ℝ := max a 1 with hx0def
  have hx0 : 0 < x0 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hx01 : 1 ≤ x0 := le_max_right _ _
  have hdouble : ∀ x ≥ x0, Fbar Fon (2 * x) ≤ p * Fbar Fon x := by
    intro x hx
    obtain ⟨hLx, hrat, hxpos⟩ := ha x (le_trans (le_max_left _ _) hx)
    have h1 : L (2 * x) < r * L x := (div_lt_iff₀ hLx).1 hrat
    have hxa : 0 < x ^ α := Real.rpow_pos_of_pos hxpos α
    have e : L (2 * x) = A2 * x ^ α * Fbar Fon (2 * x) := by
      simp only [hL, hA2def]
      rw [Real.mul_rpow (by norm_num) hxpos.le]
    rw [e] at h1
    simp only [hL] at h1
    have h2 : A2 * Fbar Fon (2 * x) < r * Fbar Fon x := by
      have : x ^ α * (A2 * Fbar Fon (2 * x)) < x ^ α * (r * Fbar Fon x) := by
        nlinarith
      exact lt_of_mul_lt_mul_left this hxa.le
    rw [hp, div_mul_eq_mul_div, le_div_iff₀ hA2pos]
    linarith
  -- positivity of Fbar
  have hpos : ∀ x, 0 < Fbar Fon x := by
    intro x
    set y := max x x0
    obtain ⟨hLy, -, hypos⟩ := ha y (le_trans (le_max_left a 1) (le_max_right _ _))
    have hy : 0 < Fbar Fon y := by
      rcases (Fbar_nonneg Fon y).lt_or_eq with h | h
      · exact h
      · exfalso; simp only [hL] at hLy; rw [← h] at hLy; simp at hLy
    exact lt_of_lt_of_le hy (Fbar_anti Fon (le_max_left _ _))
  -- Fbar becomes small
  have hsmall : ∀ ε > 0, ∃ x > 0, Fbar Fon x < ε := by
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by linarith : p < 1)
    refine ⟨2 ^ n * x0, by positivity, ?_⟩
    have := iter Fon hp0 hx0 hdouble n x0 le_rfl
    have h1 := Fbar_le_one Fon x0
    have : p ^ n * Fbar Fon x0 ≤ p ^ n := by
      have := pow_nonneg hp0 n; nlinarith
    linarith
  -- properties of b
  have hSne : ∀ s > 0, ({x : ℝ | 0 < x ∧ s * Fbar Fon x ≤ 1}).Nonempty := by
    intro s hs
    obtain ⟨x, hx, hFx⟩ := hsmall (1 / s) (by positivity)
    refine ⟨x, hx, ?_⟩
    rw [lt_div_iff₀ hs] at hFx; linarith
  have hSbdd : ∀ s, BddBelow ({x : ℝ | 0 < x ∧ s * Fbar Fon x ≤ 1}) :=
    fun s => ⟨0, fun x hx => hx.1.le⟩
  have hb_ge : ∀ M s, 0 < s → 1 < s * Fbar Fon M → M ≤ b Fon s := by
    intro M s hs hM
    apply le_csInf (hSne s hs)
    intro x hx
    by_contra hxM
    rw [not_le] at hxM
    have : Fbar Fon M ≤ Fbar Fon x := Fbar_anti Fon hxM.le
    have : s * Fbar Fon M ≤ s * Fbar Fon x := mul_le_mul_of_nonneg_left this hs.le
    linarith [hx.2]
  have hb_mem : ∀ s > 0, 0 < b Fon s → s * Fbar Fon (2 * b Fon s) ≤ 1 := by
    intro s hs hbpos
    have hlt : b Fon s < 2 * b Fon s := by linarith
    obtain ⟨x, hx, hx2⟩ := exists_lt_of_csInf_lt (hSne s hs) hlt
    have : Fbar Fon (2 * b Fon s) ≤ Fbar Fon x := Fbar_anti Fon hx2.le
    have : s * Fbar Fon (2 * b Fon s) ≤ s * Fbar Fon x := mul_le_mul_of_nonneg_left this hs.le
    linarith [hx.2]
  -- s(T) → ∞
  have hs_top : Tendsto (fun T => lam T * T) atTop atTop := by
    have h0 : Tendsto (fun T : ℝ => lam 0 * T) atTop atTop :=
      Tendsto.const_mul_atTop (hlam 0) tendsto_id
    refine tendsto_atTop_mono' atTop ?_ h0
    filter_upwards [eventually_ge_atTop 0] with T hT
    exact mul_le_mul_of_nonneg_right (hmono hT) hT
  have hb_big : ∀ᶠ T in atTop, x0 ≤ b Fon (lam T * T) := by
    have hFx0 := hpos x0
    filter_upwards [hs_top.eventually (eventually_gt_atTop (1 / Fbar Fon x0)),
      eventually_gt_atTop 0] with T hT hT0
    have hspos : 0 < lam T * T := mul_pos (hlam T) hT0
    apply hb_ge x0 _ hspos
    rw [div_lt_iff₀ hFx0] at hT; linarith
  -- main squeeze
  rw [tendsto_order]
  constructor
  · intro c hc
    filter_upwards [hb_big, eventually_gt_atTop 0] with T hbT hT0
    have hbpos : 0 < b Fon (lam T * T) := lt_of_lt_of_le hx0 hbT
    have : 0 ≤ lam T * T ^ 2 * Fbar Fon T / b Fon (lam T * T) := by
      have := hlam T; have := hpos T; positivity
    linarith
  · intro c hc
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (by linarith : 0 < c / 4) hq1
    have h2N : (0 : ℝ) < 2 ^ N := by positivity
    have hev2 : ∀ᶠ T in atTop, b Fon (lam T * T) / T < 1 / (2 * 2 ^ N) :=
      hC1.eventually (gt_mem_nhds (by positivity))
    filter_upwards [hb_big, eventually_gt_atTop 0, hev2] with T hbT hT0 hbT2
    set s := lam T * T with hs
    set bb := b Fon s with hbb
    have hspos : 0 < s := mul_pos (hlam T) hT0
    have hbpos : 0 < bb := lt_of_lt_of_le hx0 hbT
    have hu : x0 ≤ 2 * bb := by linarith
    have hTu : 2 ^ N * (2 * bb) ≤ T := by
      rw [div_lt_iff₀ hT0] at hbT2
      have : bb * (2 * 2 ^ N) < 1 / (2 * 2 ^ N) * T * (2 * 2 ^ N) := by
        exact mul_lt_mul_of_pos_right hbT2 (by positivity)
      rw [show 1 / (2 * 2 ^ N) * T * (2 * 2 ^ N) = T by field_simp] at this
      nlinarith
    have hpot := potter Fon hp0 hq1.le hx0 hdouble (2 * bb) hu N T hTu
    have hmem := hb_mem s hspos hbpos
    have hqN0 : 0 ≤ (2 * p) ^ N := pow_nonneg (by linarith) N
    have key : lam T * T ^ 2 * Fbar Fon T ≤ 4 * (2 * p) ^ N * bb := by
      have e : lam T * T ^ 2 * Fbar Fon T = s * (T * Fbar Fon T) := by rw [hs]; ring
      rw [e]
      calc s * (T * Fbar Fon T) ≤ s * (2 * (2 * p) ^ N * (2 * bb * Fbar Fon (2 * bb))) :=
            mul_le_mul_of_nonneg_left hpot hspos.le
        _ = 4 * (2 * p) ^ N * bb * (s * Fbar Fon (2 * bb)) := by ring
        _ ≤ 4 * (2 * p) ^ N * bb * 1 := by
            apply mul_le_mul_of_nonneg_left hmem
            positivity
        _ = 4 * (2 * p) ^ N * bb := by ring
    rw [div_lt_iff₀ hbpos]
    nlinarith
