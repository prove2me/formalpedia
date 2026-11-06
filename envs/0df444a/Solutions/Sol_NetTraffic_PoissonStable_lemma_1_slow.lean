-- Prove2me | solution 1 for NetTraffic.PoissonStable.lemma_1_slow
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T01:02:14.850901+00:00
-- url     : https://prove2.me/submissions/411be424-9f8a-4ad1-a0a2-a0cbc6418344
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NetTraffic_PoissonStable_Setting
import Theorems.Thm_NetTraffic_PoissonStable_eq_2_14

open MeasureTheory ProbabilityTheory Filter Topology
open NetTraffic.PoissonStable

namespace Sol_l1slow

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

lemma iterLow (Fon : Measure ℝ) [IsFiniteMeasure Fon] {K x0 : ℝ} (hK : 0 ≤ K) (hx0 : 0 < x0)
    (h : ∀ x ≥ x0, Fbar Fon x ≤ K * Fbar Fon (2 * x)) :
    ∀ n : ℕ, ∀ x ≥ x0, Fbar Fon x ≤ K ^ n * Fbar Fon (2 ^ n * x) := by
  intro n
  induction n with
  | zero => intro x _; simp
  | succ n ih =>
    intro x hx
    have h1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    have h2 : x0 ≤ 2 ^ n * x := le_trans hx (by nlinarith [lt_of_lt_of_le hx0 hx])
    have e : (2 : ℝ) ^ (n + 1) * x = 2 * (2 ^ n * x) := by ring
    rw [e]
    calc Fbar Fon x ≤ K ^ n * Fbar Fon (2 ^ n * x) := ih x hx
      _ ≤ K ^ n * (K * Fbar Fon (2 * (2 ^ n * x))) :=
          mul_le_mul_of_nonneg_left (h _ h2) (pow_nonneg hK n)
      _ = K ^ (n + 1) * Fbar Fon (2 * (2 ^ n * x)) := by ring

/-- Constants coming from regular variation of `F̄`. -/
lemma setup {Fon : Measure ℝ} [IsProbabilityMeasure Fon] {α : ℝ} (hF : HeavyTail Fon α) :
    ∃ p x0 K : ℝ, 0 ≤ p ∧ 2 * p < 1 ∧ 1 ≤ x0 ∧ 0 ≤ K ∧
      (∀ x ≥ x0, Fbar Fon (2 * x) ≤ p * Fbar Fon x) ∧
      (∀ x ≥ x0, Fbar Fon x ≤ K * Fbar Fon (2 * x)) ∧
      (∀ x, 0 < Fbar Fon x) := by
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
  set L : ℝ → ℝ := fun x => x ^ α * Fbar Fon x with hL
  have hSV := hF.slowlyVarying
  have hev : ∀ᶠ x in atTop, 0 < L x ∧ (L (2 * x) / L x < r ∧ (1 / 2 : ℝ) < L (2 * x) / L x)
      ∧ 0 < x :=
    hSV.1.and ((((hSV.2 2 two_pos).eventually (gt_mem_nhds hr1)).and
      ((hSV.2 2 two_pos).eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)))).and
      (eventually_gt_atTop 0))
  obtain ⟨a, ha⟩ := eventually_atTop.1 hev
  set x0 : ℝ := max a 1 with hx0def
  have hx01 : 1 ≤ x0 := le_max_right _ _
  have eL : ∀ x, 0 < x → L (2 * x) = A2 * x ^ α * Fbar Fon (2 * x) := by
    intro x hxpos
    simp only [hL, hA2def]
    rw [Real.mul_rpow (by norm_num) hxpos.le]
  refine ⟨p, x0, 2 * A2, hp0, hq1, hx01, by linarith, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨hLx, ⟨hrat, -⟩, hxpos⟩ := ha x (le_trans (le_max_left _ _) hx)
    have h1 : L (2 * x) < r * L x := (div_lt_iff₀ hLx).1 hrat
    have hxa : 0 < x ^ α := Real.rpow_pos_of_pos hxpos α
    rw [eL x hxpos] at h1
    simp only [hL] at h1
    have h2 : A2 * Fbar Fon (2 * x) < r * Fbar Fon x := by
      have : x ^ α * (A2 * Fbar Fon (2 * x)) < x ^ α * (r * Fbar Fon x) := by
        nlinarith
      exact lt_of_mul_lt_mul_left this hxa.le
    rw [hp, div_mul_eq_mul_div, le_div_iff₀ hA2pos]
    linarith
  · intro x hx
    obtain ⟨hLx, ⟨-, hrat⟩, hxpos⟩ := ha x (le_trans (le_max_left _ _) hx)
    have h1 : 1 / 2 * L x < L (2 * x) := (lt_div_iff₀ hLx).1 hrat
    have hxa : 0 < x ^ α := Real.rpow_pos_of_pos hxpos α
    rw [eL x hxpos] at h1
    simp only [hL] at h1
    have h2 : 1 / 2 * Fbar Fon x < A2 * Fbar Fon (2 * x) := by
      have : x ^ α * (1 / 2 * Fbar Fon x) < x ^ α * (A2 * Fbar Fon (2 * x)) := by
        nlinarith
      exact lt_of_mul_lt_mul_left this hxa.le
    linarith
  · intro x
    set y := max x x0
    obtain ⟨hLy, -, hypos⟩ := ha y (le_trans (le_max_left a 1) (le_max_right _ _))
    have hy : 0 < Fbar Fon y := by
      rcases (Fbar_nonneg Fon y).lt_or_eq with h | h
      · exact h
      · exfalso; simp only [hL] at hLy; rw [← h] at hLy; simp at hLy
    exact lt_of_lt_of_le hy (Fbar_anti Fon (le_max_left _ _))

/-- The equivalence `b(λT)/T → 0 ⟺ λT F̄(T) → 0` (first half of Lemma 1). -/
lemma cond1_iff {Fon : Measure ℝ} [IsProbabilityMeasure Fon] {α : ℝ} (hF : HeavyTail Fon α)
    {lam : ℝ → ℝ} (hlam : ∀ T, 0 < lam T) (hmono : Monotone lam) :
    Condition1 Fon lam ↔ Tendsto (fun T => lam T * T * Fbar Fon T) atTop (𝓝 0) := by
  obtain ⟨p, x0, K, hp0, hq1, hx01, hK, hdouble, hlow, hpos⟩ := setup hF
  have hx0 : 0 < x0 := by linarith
  have hsmall : ∀ ε > 0, ∃ x > 0, Fbar Fon x < ε := by
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by linarith : p < 1)
    refine ⟨2 ^ n * x0, by positivity, ?_⟩
    have := iter Fon hp0 hx0 hdouble n x0 le_rfl
    have h1 := Fbar_le_one Fon x0
    have : p ^ n * Fbar Fon x0 ≤ p ^ n := by
      have := pow_nonneg hp0 n; nlinarith
    linarith
  have hSne : ∀ s > 0, ({x : ℝ | 0 < x ∧ s * Fbar Fon x ≤ 1}).Nonempty := by
    intro s hs
    obtain ⟨x, hx, hFx⟩ := hsmall (1 / s) (by positivity)
    refine ⟨x, hx, ?_⟩
    rw [lt_div_iff₀ hs] at hFx; linarith
  have hSbdd : ∀ s, BddBelow ({x : ℝ | 0 < x ∧ s * Fbar Fon x ≤ 1}) :=
    fun s => ⟨0, fun x hx => hx.1.le⟩
  have hb_nonneg : ∀ s, 0 ≤ b Fon s := fun s => Real.sInf_nonneg (fun x hx => hx.1.le)
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
  have hb_le : ∀ s y, 0 < y → s * Fbar Fon y ≤ 1 → b Fon s ≤ y :=
    fun s y hy h => csInf_le (hSbdd s) ⟨hy, h⟩
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
  constructor
  · intro hC1
    rw [tendsto_order]
    constructor
    · intro c hc
      filter_upwards [eventually_gt_atTop 0] with T hT0
      have := hlam T; have := hpos T
      have : 0 ≤ lam T * T * Fbar Fon T := by positivity
      linarith
    · intro c hc
      obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hc (by linarith : p < 1)
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
      have hit := iter Fon hp0 hx0 hdouble N (2 * bb) hu
      have hFT : Fbar Fon T ≤ Fbar Fon (2 ^ N * (2 * bb)) := Fbar_anti Fon hTu
      have hmem := hb_mem s hspos hbpos
      have hpN := pow_nonneg hp0 N
      calc s * Fbar Fon T ≤ s * (p ^ N * Fbar Fon (2 * bb)) :=
            mul_le_mul_of_nonneg_left (le_trans hFT hit) hspos.le
        _ = p ^ N * (s * Fbar Fon (2 * bb)) := by ring
        _ ≤ p ^ N * 1 := mul_le_mul_of_nonneg_left hmem hpN
        _ < c := by linarith
  · intro hlim
    unfold Condition1
    rw [tendsto_order]
    constructor
    · intro c hc
      filter_upwards [eventually_gt_atTop 0] with T hT0
      have := hb_nonneg (lam T * T)
      have : 0 ≤ b Fon (lam T * T) / T := by positivity
      linarith
    · intro c hc
      obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hc (by norm_num : (1 / 2 : ℝ) < 1)
      have hKN : 0 < 1 / (K + 1) ^ N := by positivity
      have h2N : (0 : ℝ) < 2 ^ N := by positivity
      filter_upwards [hlim.eventually (gt_mem_nhds hKN), eventually_ge_atTop (2 ^ N * x0),
        eventually_gt_atTop 0] with T hT1 hT2 hT0
      set y := T / 2 ^ N with hy
      have hypos : 0 < y := by positivity
      have hyx0 : x0 ≤ y := by rw [hy, le_div_iff₀ h2N]; linarith
      have hlowN := iterLow Fon hK hx0 hlow N y hyx0
      have e : (2 : ℝ) ^ N * y = T := by rw [hy]; field_simp
      rw [e] at hlowN
      have hKle : K ^ N ≤ (K + 1) ^ N := pow_le_pow_left₀ hK (by linarith) N
      have hspos : 0 < lam T * T := mul_pos (hlam T) hT0
      have hsy : lam T * T * Fbar Fon y ≤ 1 := by
        have hFT := (hpos T).le
        have h3 : lam T * T * Fbar Fon y ≤ (K + 1) ^ N * (lam T * T * Fbar Fon T) := by
          calc lam T * T * Fbar Fon y ≤ lam T * T * (K ^ N * Fbar Fon T) :=
                mul_le_mul_of_nonneg_left hlowN hspos.le
            _ ≤ lam T * T * ((K + 1) ^ N * Fbar Fon T) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKle hFT) hspos.le
            _ = (K + 1) ^ N * (lam T * T * Fbar Fon T) := by ring
        have hKpos : 0 < (K + 1) ^ N := by positivity
        rw [lt_div_iff₀ hKpos] at hT1
        linarith
      have hbley := hb_le _ y hypos hsy
      have : b Fon (lam T * T) / T ≤ (1 / 2) ^ N := by
        rw [div_le_iff₀ hT0]
        calc b Fon (lam T * T) ≤ y := hbley
          _ = (1 / 2) ^ N * T := by rw [hy, div_pow, one_pow]; field_simp
      linarith

end Sol_l1slow

open Sol_l1slow in
theorem solution
    {Fon : Measure ℝ} [IsProbabilityMeasure Fon] {α : ℝ} (hF : HeavyTail Fon α)
    {lam : ℝ → ℝ} (hlam : ∀ T, 0 < lam T) (hmono : Monotone lam)
    {Ω : ℝ → Type*} [∀ T, MeasurableSpace (Ω T)] (P : ∀ T, Measure (Ω T))
    [∀ T, IsProbabilityMeasure (P T)] (Γ X : ∀ T, ℤ → Ω T → ℝ)
    (hmodel : ∀ T, IsPoissonModel (P T) (lam T) Fon (Γ T) (X T)) :
    (Condition1 Fon lam ↔ Tendsto (fun T => lam T * T * Fbar Fon T) atTop (𝓝 0)) ∧
    (Condition1 Fon lam ↔ Tendsto (fun T =>
      cov[fun ω => (N (Γ T) (X T) 0 ω : ℝ), fun ω => (N (Γ T) (X T) T ω : ℝ); P T])
        atTop (𝓝 0)) := by
  have h1 := cond1_iff hF hlam hmono
  refine ⟨h1, h1.trans ?_⟩
  obtain ⟨_, _, _, -, -, -, -, -, -, hpos⟩ := setup hF
  -- the covariance formula and Karamata asymptotics from (2.14)
  have hcov : ∀ T : ℝ, 0 ≤ T →
      cov[fun ω => (N (Γ T) (X T) 0 ω : ℝ), fun ω => (N (Γ T) (X T) T ω : ℝ); P T] =
        lam T * ∫ v in Set.Ioi T, Fbar Fon v := by
    intro T hT
    have := (eq_2_14 hF (hlam T) (hmodel T)).1 0 T hT
    simpa using this
  obtain ⟨c, hc, hlim1⟩ := (eq_2_14 hF (hlam 1) (hmodel 1)).2
  have hlim0 := hlim1 0
  -- R(h) = ∫_h^∞ F̄ / (h F̄(h)) → c / λ(1)
  set R : ℝ → ℝ := fun h => (∫ v in Set.Ioi h, Fbar Fon v) / (h * Fbar Fon h) with hR
  have hRlim : Tendsto R atTop (𝓝 (c / lam 1)) := by
    have : Tendsto (fun h => (cov[fun ω => (N (Γ 1) (X 1) 0 ω : ℝ),
        fun ω => (N (Γ 1) (X 1) (0 + h) ω : ℝ); P 1] / (h * Fbar Fon h)) / lam 1) atTop
        (𝓝 (c / lam 1)) := hlim0.div_const _
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with h hh
    have := (eq_2_14 hF (hlam 1) (hmodel 1)).1 0 h hh
    rw [this, hR]
    have := hlam 1
    field_simp
  have hc' : c / lam 1 ≠ 0 := (div_pos hc (hlam 1)).ne'
  -- cov_T = (λ T F̄(T)) · R(T)
  have hfac : ∀ᶠ T in atTop,
      cov[fun ω => (N (Γ T) (X T) 0 ω : ℝ), fun ω => (N (Γ T) (X T) T ω : ℝ); P T] =
        (lam T * T * Fbar Fon T) * R T := by
    filter_upwards [eventually_gt_atTop 0] with T hT
    rw [hcov T hT.le, hR]
    have := hpos T
    field_simp
  constructor
  · intro h
    have := h.mul hRlim
    rw [zero_mul] at this
    exact this.congr' (hfac.mono fun T hT => hT.symm)
  · intro h
    have h2 : Tendsto (fun T => (lam T * T * Fbar Fon T) * R T / R T) atTop
        (𝓝 (0 / (c / lam 1))) := (h.congr' hfac).div hRlim hc'
    rw [zero_div] at h2
    refine h2.congr' ?_
    filter_upwards [hRlim.eventually_ne hc'] with T hT
    field_simp
