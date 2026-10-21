-- Prove2me | solution 1 for LNChannels.SmallRate.theorem_3_i_size
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:38:43.775433+00:00
-- url     : https://prove2.me/submissions/adc1fe30-4475-4344-bad7-48a00ba90922

import Mathlib
import Definitions.Def_LNChannels_Exact_uniCost
import Definitions.Def_LNChannels_SmallRate_minUniCost
import Definitions.Def_LNChannels_SmallRate_uniOptimalSize

set_option autoImplicit false
open Filter Asymptotics LNChannels.Exact

namespace LNMinHelp

lemma alg (k q y : ℝ) (hq1 : 1 < q) (hy : 1 < y) (hqk : (q - 1) ^ 2 = k * q) :
    0 ≤ (1 - q / y) + k / (y - 1) - k / (q - 1) := by
  have hq0 : 0 < q := by linarith
  have hk : k = (q - 1) ^ 2 / q := by field_simp; linarith
  have h1 : y - 1 ≠ 0 := by linarith
  have h2 : q - 1 ≠ 0 := by linarith
  have h3 : y ≠ 0 := by linarith
  have : (1 - q / y) + k / (y - 1) - k / (q - 1) = (y - q) ^ 2 / (y * q * (y - 1)) := by
    rw [hk]
    field_simp
    ring
  rw [this]
  have : 0 < y - 1 := by linarith
  positivity

end LNMinHelp

theorem lne_uni_min (lam₂ r B : ℝ) (hB : 0 < B) (hlam₂ : 0 < lam₂) (hr : 0 < r) :
    let k := B * Real.log (1 + r / lam₂)
    let copt := B / (2 * k) * (-k + Real.sqrt (k * (k + 4))
      + 2 * Real.log ((1 / 2) * (k + Real.sqrt (k * (k + 4)) + 2)))
    let lstar := B / k * Real.log ((1 / 2) * (k + Real.sqrt (k * (k + 4)) + 2))
    IsLeast (uniCost lam₂ r B '' Set.Ioi 0) copt ∧ 0 < lstar ∧
      uniCost lam₂ r B lstar = copt := by
  intro k copt lstar
  have hρ : 1 < 1 + r / lam₂ := by
    have : 0 < r / lam₂ := by positivity
    linarith
  have hlogρ : 0 < Real.log (1 + r / lam₂) := Real.log_pos hρ
  have hk : 0 < k := mul_pos hB hlogρ
  have hρeq : (r + lam₂) / lam₂ = 1 + r / lam₂ := by field_simp; ring
  obtain ⟨D, hDdef⟩ : ∃ D, D = Real.sqrt (k * (k + 4)) := ⟨_, rfl⟩
  have hD2 : D ^ 2 = k * (k + 4) := by rw [hDdef]; exact Real.sq_sqrt (by positivity)
  have hDpos : 0 < D := by rw [hDdef]; exact Real.sqrt_pos.2 (by positivity)
  obtain ⟨q, hqdef⟩ : ∃ q, q = (1 / 2) * (k + D + 2) := ⟨_, rfl⟩
  have hq1 : 1 < q := by rw [hqdef]; linarith
  have hqk : (q - 1) ^ 2 = k * q := by
    rw [hqdef]; linear_combination (1 / 4) * hD2
  have hkq : k / (q - 1) = (D - k) / 2 := by
    rw [div_eq_iff (by linarith)]
    rw [hqdef]; linear_combination (-1 / 4) * hD2
  have hcopt : copt = B / k * (Real.log q + (D - k) / 2) := by
    simp only [copt]
    rw [← hDdef, ← hqdef]
    field_simp
    ring
  have hlstar : lstar = B / k * Real.log q := by
    simp only [lstar]
    rw [← hDdef, ← hqdef]
  have hlogq : 0 < Real.log q := Real.log_pos hq1
  have hlstar_pos : 0 < lstar := by rw [hlstar]; positivity
  have hq0 : 0 < q := by linarith
  have hlogρ' : Real.log (1 + r / lam₂) = k / B := by
    simp only [k]; field_simp
  have hcost : ∀ m : ℝ, 0 < m → uniCost lam₂ r B m =
      B / k * (Real.log ((1 + r / lam₂) ^ m) + k / ((1 + r / lam₂) ^ m - 1)) := by
    intro m hm
    have hy : 1 < (1 + r / lam₂) ^ m := Real.one_lt_rpow hρ hm
    have hy1 : (1 + r / lam₂) ^ m - 1 ≠ 0 := by linarith
    unfold uniCost
    rw [hρeq, Real.log_rpow (by linarith), hlogρ']
    field_simp
  have hlow : ∀ m : ℝ, 0 < m → copt ≤ uniCost lam₂ r B m := by
    intro m hm
    have hy : 1 < (1 + r / lam₂) ^ m := Real.one_lt_rpow hρ hm
    rw [hcost m hm, hcopt]
    generalize (1 + r / lam₂) ^ m = y at hy ⊢
    have hy0 : 0 < y := by linarith
    have h1 : 1 - q / y ≤ Real.log y - Real.log q := by
      have := Real.one_sub_inv_le_log_of_pos (show 0 < y / q by positivity)
      rwa [Real.log_div hy0.ne' hq0.ne', inv_div] at this
    have h2 := LNMinHelp.alg k q y hq1 hy hqk
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  have hy_star : (1 + r / lam₂) ^ lstar = q := by
    have hpos : 0 < (1 + r / lam₂) ^ lstar := Real.rpow_pos_of_pos (by linarith) _
    apply Real.log_injOn_pos (Set.mem_Ioi.2 hpos) (Set.mem_Ioi.2 hq0)
    rw [Real.log_rpow (by linarith), hlogρ', hlstar]
    field_simp
  have heq : uniCost lam₂ r B lstar = copt := by
    rw [hcost lstar hlstar_pos, hy_star, hkq, hcopt]
  refine ⟨⟨⟨lstar, hlstar_pos, heq⟩, ?_⟩, hlstar_pos, heq⟩
  rintro _ ⟨m, hm, rfl⟩
  exact hlow m hm


namespace LNS3

lemma mono_inv (a b : ℝ) (ha : 1 ≤ a) (hab : a < b) : a + a⁻¹ < b + b⁻¹ := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have h1 : b + b⁻¹ - (a + a⁻¹) = (b - a) * (a * b - 1) / (a * b) := by field_simp; ring
  have h2 : 0 < (b - a) * (a * b - 1) / (a * b) :=
    div_pos (mul_pos (by linarith) (by nlinarith)) (by positivity)
  linarith

lemma core (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    1 ≤ (t ^ 2 + 2 + t * Real.sqrt (t ^ 2 + 4)) / 2 ∧
    t - t ^ 3 / 2 ≤ Real.log ((t ^ 2 + 2 + t * Real.sqrt (t ^ 2 + 4)) / 2) ∧
    Real.log ((t ^ 2 + 2 + t * Real.sqrt (t ^ 2 + 4)) / 2) ≤ t := by
  obtain ⟨q, hqdef⟩ : ∃ q, q = (t ^ 2 + 2 + t * Real.sqrt (t ^ 2 + 4)) / 2 := ⟨_, rfl⟩
  rw [← hqdef]
  have hs2 : Real.sqrt (t ^ 2 + 4) ^ 2 = t ^ 2 + 4 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ Real.sqrt (t ^ 2 + 4) := Real.sqrt_nonneg _
  have hq1 : 1 ≤ q := by rw [hqdef]; nlinarith [mul_nonneg ht0.le hs0]
  have hq0 : 0 < q := by linarith
  have hqq : q + q⁻¹ = t ^ 2 + 2 := by
    field_simp
    rw [hqdef]
    linear_combination (t ^ 2 / 4) * hs2
  have ht2 : t ^ 2 ≤ 1 := by nlinarith
  have ht3 : t ^ 3 ≤ t := by nlinarith [pow_pos ht0 2]
  have ht4 : t ^ 4 ≤ t ^ 2 := by nlinarith [pow_pos ht0 2]
  have ht6 : t ^ 6 ≤ t ^ 4 := by nlinarith [pow_pos ht0 4]
  refine ⟨hq1, ?_, ?_⟩
  · -- lower bound
    obtain ⟨v, hvdef⟩ : ∃ v, v = t - t ^ 3 / 2 := ⟨_, rfl⟩
    rw [← hvdef]
    have hv0 : 0 ≤ v := by rw [hvdef]; linarith
    have hvt : v ≤ t := by rw [hvdef]; nlinarith [pow_pos ht0 3]
    have h1 := Real.exp_bound (x := v) (by rw [abs_of_nonneg hv0]; linarith) (n := 4) (by norm_num)
    have h2 := Real.exp_bound (x := -v) (by rw [abs_neg, abs_of_nonneg hv0]; linarith) (n := 4)
      (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_nonneg hv0] at h1 h2
    have h1' := (abs_le.mp h1).2
    have h2' := (abs_le.mp h2).2
    have hv4 : v ^ 4 ≤ t ^ 4 := pow_le_pow_left₀ hv0 hvt 4
    have hvsq : v ^ 2 = t ^ 2 - t ^ 4 + t ^ 6 / 4 := by rw [hvdef]; ring
    have hsum : Real.exp v + Real.exp (-v) ≤ t ^ 2 + 2 := by
      nlinarith
    by_contra hlt
    push Not at hlt
    have : q < Real.exp v := (Real.log_lt_iff_lt_exp hq0).mp hlt
    have := mono_inv q (Real.exp v) hq1 this
    rw [Real.exp_neg] at hsum
    linarith
  · -- upper bound
    rw [Real.log_le_iff_le_exp hq0]
    have h1 := Real.exp_bound (x := t) (by rw [abs_of_nonneg ht0.le]; exact ht1) (n := 6)
      (by norm_num)
    have h2 := Real.exp_bound (x := -t) (by rw [abs_neg, abs_of_nonneg ht0.le]; exact ht1) (n := 6)
      (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_nonneg ht0.le] at h1 h2
    have h1' := (abs_le.mp h1).1
    have h2' := (abs_le.mp h2).1
    have hsum : t ^ 2 + 2 ≤ Real.exp t + Real.exp (-t) := by
      nlinarith
    by_contra hlt
    push Not at hlt
    have hE1 : 1 ≤ Real.exp t := Real.one_le_exp ht0.le
    have := mono_inv (Real.exp t) q hE1 hlt
    rw [Real.exp_neg] at hsum
    linarith

lemma sqrt_prod (t : ℝ) (ht0 : 0 < t) : Real.sqrt (t ^ 2 * (t ^ 2 + 4)) = t * Real.sqrt (t ^ 2 + 4) := by
  rw [Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht0.le]

lemma sqrt_bounds (t : ℝ) (ht0 : 0 < t) : 2 ≤ Real.sqrt (t ^ 2 + 4) ∧ Real.sqrt (t ^ 2 + 4) ≤ 2 + t ^ 2 / 4 := by
  constructor
  · calc (2 : ℝ) = Real.sqrt (2 ^ 2) := by rw [Real.sqrt_sq (by norm_num)]
      _ ≤ Real.sqrt (t ^ 2 + 4) := Real.sqrt_le_sqrt (by nlinarith)
  · rw [Real.sqrt_le_left (by positivity)]
    nlinarith [sq_nonneg (t ^ 2)]

lemma cost_est (B t : ℝ) (hB : 0 < B) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    |B / (2 * t ^ 2) * (-t ^ 2 + Real.sqrt (t ^ 2 * (t ^ 2 + 4)) +
      2 * Real.log ((1 / 2) * (t ^ 2 + Real.sqrt (t ^ 2 * (t ^ 2 + 4)) + 2))) -
        (2 * B / t - B / 2)| ≤ B * t / 2 := by
  obtain ⟨-, hlow, hup⟩ := core t ht0 ht1
  obtain ⟨hs1, hs2⟩ := sqrt_bounds t ht0
  rw [sqrt_prod t ht0]
  have harg : (1 / 2 : ℝ) * (t ^ 2 + t * Real.sqrt (t ^ 2 + 4) + 2) =
      (t ^ 2 + 2 + t * Real.sqrt (t ^ 2 + 4)) / 2 := by ring
  rw [harg]
  generalize Real.log ((t ^ 2 + 2 + t * Real.sqrt (t ^ 2 + 4)) / 2) = u at hlow hup ⊢
  generalize Real.sqrt (t ^ 2 + 4) = s at hs1 hs2 ⊢
  have hE : B / (2 * t ^ 2) * (-t ^ 2 + t * s + 2 * u) - (2 * B / t - B / 2) =
      B / (2 * t ^ 2) * (t * s + 2 * u - 4 * t) := by
    field_simp
    ring
  rw [hE]
  have hc : 0 < B / (2 * t ^ 2) := by positivity
  have hct : B / (2 * t ^ 2) * t ^ 3 = B * t / 2 := by field_simp
  have hE1 : t * s + 2 * u - 4 * t ≤ t ^ 3 := by nlinarith [mul_le_mul_of_nonneg_left hs2 ht0.le]
  have hE2 : -t ^ 3 ≤ t * s + 2 * u - 4 * t := by nlinarith [mul_le_mul_of_nonneg_left hs1 ht0.le]
  rw [abs_le]
  constructor
  · have := mul_le_mul_of_nonneg_left hE2 hc.le
    nlinarith
  · have := mul_le_mul_of_nonneg_left hE1 hc.le
    nlinarith

lemma size_est (B t : ℝ) (hB : 0 < B) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    |B / t ^ 2 * Real.log ((1 / 2) * (t ^ 2 + Real.sqrt (t ^ 2 * (t ^ 2 + 4)) + 2)) - B / t| ≤
      B * t / 2 := by
  obtain ⟨-, hlow, hup⟩ := core t ht0 ht1
  rw [sqrt_prod t ht0]
  have harg : (1 / 2 : ℝ) * (t ^ 2 + t * Real.sqrt (t ^ 2 + 4) + 2) =
      (t ^ 2 + 2 + t * Real.sqrt (t ^ 2 + 4)) / 2 := by ring
  rw [harg]
  generalize Real.log ((t ^ 2 + 2 + t * Real.sqrt (t ^ 2 + 4)) / 2) = u at hlow hup ⊢
  have hE : B / t ^ 2 * u - B / t = B / t ^ 2 * (u - t) := by field_simp
  rw [hE]
  have hc : 0 < B / t ^ 2 := by positivity
  have hct : B / t ^ 2 * (t ^ 3 / 2) = B * t / 2 := by field_simp
  rw [abs_le]
  constructor
  · have := mul_le_mul_of_nonneg_left (show -(t ^ 3 / 2) ≤ u - t by linarith) hc.le
    nlinarith
  · have := mul_le_mul_of_nonneg_left (show u - t ≤ 0 by linarith) hc.le
    nlinarith [mul_pos hB ht0]

/-- Relating `t = √(B log(1+x))` to `x = r/λ`. -/
lemma param (B x : ℝ) (hB : 0 < B) (hx : 0 < x) (hx1 : x ≤ 1) (hBx : B * x ≤ 1) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ B * Real.log (1 + x) = t ^ 2 ∧
      t ≤ Real.sqrt B * Real.sqrt x ∧
      |B / t - Real.sqrt B / Real.sqrt x| ≤ 2 * Real.sqrt B * Real.sqrt x := by
  have hL1 : Real.log (1 + x) ≤ x := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + x by linarith); linarith
  have hL2 : x / (1 + x) ≤ Real.log (1 + x) := by
    have := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + x by linarith)
    have e : 1 - (1 + x)⁻¹ = x / (1 + x) := by field_simp; ring
    linarith
  have hL3 : x / 2 ≤ Real.log (1 + x) := by
    refine le_trans ?_ hL2
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    nlinarith
  have hL0 : 0 < Real.log (1 + x) := lt_of_lt_of_le (by positivity) hL3
  have hk : 0 < B * Real.log (1 + x) := mul_pos hB hL0
  obtain ⟨t, htdef⟩ : ∃ t, t = Real.sqrt (B * Real.log (1 + x)) := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [htdef]; exact Real.sqrt_pos.2 hk
  have hkt : B * Real.log (1 + x) = t ^ 2 := by rw [htdef, Real.sq_sqrt hk.le]
  have hkx : B * Real.log (1 + x) ≤ B * x := mul_le_mul_of_nonneg_left hL1 hB.le
  have ht1 : t ≤ 1 := by nlinarith
  have hsB : 0 < Real.sqrt B := Real.sqrt_pos.2 hB
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hsB2 : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB.le
  have hsx2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  obtain ⟨b, hbdef⟩ : ∃ b, b = Real.sqrt (Real.log (1 + x)) := ⟨_, rfl⟩
  have hb0 : 0 < b := by rw [hbdef]; exact Real.sqrt_pos.2 hL0
  have hb2 : b ^ 2 = Real.log (1 + x) := by rw [hbdef, Real.sq_sqrt hL0.le]
  obtain ⟨a, hadef⟩ : ∃ a, a = Real.sqrt x := ⟨_, rfl⟩
  rw [← hadef] at hsx hsx2
  have ha2 : a ^ 2 = x := hsx2
  have htb : t = Real.sqrt B * b := by
    rw [htdef, Real.sqrt_mul hB.le, hbdef]
  refine ⟨t, ht0, ht1, hkt, ?_, ?_⟩
  · rw [htb, ← hadef]
    have : b ≤ a := by
      by_contra h; push Not at h; nlinarith
    exact mul_le_mul_of_nonneg_left this hsB.le
  · rw [← hadef]
    have hba : b ≤ a := by
      by_contra h; push Not at h; nlinarith
    have hb_half : a / 2 ≤ b := by
      by_contra h; push Not at h
      nlinarith
    have hdiff : a - b ≤ a ^ 3 := by
      have h1 : x - Real.log (1 + x) ≤ x ^ 2 := by
        have : x - x / (1 + x) = x ^ 2 / (1 + x) := by field_simp; ring
        have h2 : x ^ 2 / (1 + x) ≤ x ^ 2 := by
          rw [div_le_iff₀ (by linarith)]; nlinarith [sq_nonneg x]
        linarith
      have h3 : (a - b) * (a + b) ≤ a ^ 4 := by nlinarith
      nlinarith
    have hBt : B / t - Real.sqrt B / a = Real.sqrt B * (a - b) / (a * b) := by
      rw [htb]
      field_simp
      nlinarith [hsB2]
    rw [hBt]
    have hnn : 0 ≤ Real.sqrt B * (a - b) / (a * b) := by
      apply div_nonneg (mul_nonneg hsB.le (by linarith)) (by positivity)
    rw [abs_of_nonneg hnn, div_le_iff₀ (by positivity)]
    have : Real.sqrt B * (a - b) ≤ Real.sqrt B * a ^ 3 := mul_le_mul_of_nonneg_left hdiff hsB.le
    have h5 : 2 * Real.sqrt B * a * (a * b) ≥ Real.sqrt B * a ^ 3 := by
      have : a * (a / 2) ≤ a * b := mul_le_mul_of_nonneg_left hb_half hsx.le
      nlinarith [mul_pos hsB hsx]
    linarith

end LNS3

open LNS3 in
theorem solution (lam B : ℝ) (hlam : 0 < lam) (hB : 0 < B) :
    (∀ r : ℝ, 0 < r → 0 < LNChannels.SmallRate.uniOptimalSize lam r B ∧
      LNChannels.Exact.uniCost lam r B (LNChannels.SmallRate.uniOptimalSize lam r B) =
        LNChannels.SmallRate.minUniCost lam r B) ∧
    (fun r : ℝ => LNChannels.SmallRate.uniOptimalSize lam r B - (B * lam / r) ^ (1 / 2 : ℝ))
      =O[nhdsWithin 0 (Set.Ioi 0)] (fun r : ℝ => r ^ (1 / 2 : ℝ)) := by
  have gen : ∀ (B k : ℝ), B / k * Real.log ((k + Real.sqrt (k * (k + 4)) + 2) / 2) =
      B / k * Real.log ((1 / 2) * (k + Real.sqrt (k * (k + 4)) + 2)) := fun B k => by
    rw [show (k + Real.sqrt (k * (k + 4)) + 2) / 2 = (1 / 2) * (k + Real.sqrt (k * (k + 4)) + 2)
      by ring]
  have hopt : ∀ r : ℝ, 0 < r → LNChannels.SmallRate.uniOptimalSize lam r B =
      B / (B * Real.log (1 + r / lam)) * Real.log ((1 / 2) * (B * Real.log (1 + r / lam) +
        Real.sqrt ((B * Real.log (1 + r / lam)) * (B * Real.log (1 + r / lam) + 4)) + 2)) := by
    intro r hr
    unfold LNChannels.SmallRate.uniOptimalSize
    dsimp only
    rw [gen]
  refine ⟨fun r hr => ?_, ?_⟩
  · have hmin := lne_uni_min lam r B hB hlam hr
    simp only at hmin
    obtain ⟨hleast, hpos, heq⟩ := hmin
    rw [hopt r hr]
    refine ⟨hpos, ?_⟩
    unfold LNChannels.SmallRate.minUniCost
    rw [hleast.csInf_eq]
    exact heq
  · have hr0 : 0 < lam * min 1 (1 / B) := by positivity
    have hmem : Set.Ioo 0 (lam * min 1 (1 / B)) ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) := Ioo_mem_nhdsGT hr0
    refine Asymptotics.IsBigO.of_bound
      ((Real.sqrt B * B / 2 + 4 * Real.sqrt B) / Real.sqrt lam) ?_
    filter_upwards [hmem] with r hr
    obtain ⟨hr0', hr1⟩ := hr
    have hx : 0 < r / lam := by positivity
    have hx1 : r / lam ≤ 1 := by
      rw [div_le_one hlam]; have := min_le_left 1 (1 / B); nlinarith
    have hBx : B * (r / lam) ≤ 1 := by
      have h1 : r / lam < min 1 (1 / B) := by rw [div_lt_iff₀ hlam]; linarith
      have h2 : r / lam < 1 / B := lt_of_lt_of_le h1 (min_le_right _ _)
      rw [lt_div_iff₀ hB] at h2; linarith
    obtain ⟨t, ht0, ht1, hkt, htle, hdiff⟩ := param B (r / lam) hB hx hx1 hBx
    have hmin := lne_uni_min lam r B hB hlam hr0'
    simp only at hmin
    rw [hkt] at hmin
    have hsq : (B * lam / r) ^ (1 / 2 : ℝ) = Real.sqrt B / Real.sqrt (r / lam) := by
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_div hB.le]
      congr 1
      field_simp
    have hrt : r ^ (1 / 2 : ℝ) = Real.sqrt r := (Real.sqrt_eq_rpow r).symm
    have hsx : Real.sqrt (r / lam) = Real.sqrt r / Real.sqrt lam := Real.sqrt_div hr0'.le lam
    have hsxpos : 0 < Real.sqrt (r / lam) := Real.sqrt_pos.2 hx
    have hsBpos : 0 < Real.sqrt B := Real.sqrt_pos.2 hB
    have hfin : (Real.sqrt B * B / 2 + 4 * Real.sqrt B) / Real.sqrt lam * ‖r ^ (1 / 2 : ℝ)‖ =
        (Real.sqrt B * B / 2 + 4 * Real.sqrt B) * Real.sqrt (r / lam) := by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hr0'.le _), hrt, hsx]
      ring
    beta_reduce
    rw [hfin, hsq, Real.norm_eq_abs]

    have hsz := hopt r hr0'
    rw [hkt] at hsz
    have hest := size_est B t hB ht0 ht1
    rw [← hsz] at hest
    generalize LNChannels.SmallRate.uniOptimalSize lam r B = m at hest ⊢
    have hsplit : m - Real.sqrt B / Real.sqrt (r / lam) =
        (m - B / t) + (B / t - Real.sqrt B / Real.sqrt (r / lam)) := by ring
    rw [hsplit]
    have h1 := abs_add_le (m - B / t) (B / t - Real.sqrt B / Real.sqrt (r / lam))
    have h2 : B * t / 2 ≤ B * (Real.sqrt B * Real.sqrt (r / lam)) / 2 := by nlinarith
    nlinarith [mul_pos hsBpos hsxpos]
