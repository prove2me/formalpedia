-- Prove2me | solution 1 for HubSpokePricing.Lagrangian.lemma_A_12
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T19:03:08.259186+00:00
-- url     : https://prove2.me/submissions/b2d8624d-6af4-4b45-ad41-8180197729f6

import Mathlib
import Definitions.Def_HubSpokePricing_Lagrangian_Prob
import Theorems.Thm_HubSpokePricing_Lagrangian_lemma_A_14

namespace HubSpokeA12Aux

open HubSpokePricing.Lagrangian Finset

lemma conv_nonneg (a b : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) (k : ℕ) :
    0 ≤ conv a b k :=
  sum_nonneg fun j _ => mul_nonneg (ha _) (hb _)

lemma sumLaw_nonneg : ∀ (n : ℕ) (ps : Fin n → ℕ → ℝ), (∀ i k, 0 ≤ ps i k) →
    ∀ k, 0 ≤ sumLaw n ps k
  | 0, _, _, k => by simp only [sumLaw]; split_ifs <;> norm_num
  | n + 1, ps, h, k => by
    simp only [sumLaw]
    exact conv_nonneg _ _ (sumLaw_nonneg n _ fun i k => h _ k) (h _) k

lemma pgf_conv (a b : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) (z : ℝ) (hz : 0 ≤ z)
    (hsa : Summable fun k => a k * z ^ k) (hsb : Summable fun k => b k * z ^ k) :
    Summable (fun k => conv a b k * z ^ k) ∧
      ∑' k, conv a b k * z ^ k = (∑' k, a k * z ^ k) * (∑' k, b k * z ^ k) := by
  have hna : Summable fun k => ‖a k * z ^ k‖ := by
    simpa [Real.norm_eq_abs] using hsa.abs
  have hnb : Summable fun k => ‖b k * z ^ k‖ := by
    simpa [Real.norm_eq_abs] using hsb.abs
  have heq : (fun k => conv a b k * z ^ k) =
      fun k => ∑ j ∈ range (k + 1), (a j * z ^ j) * (b (k - j) * z ^ (k - j)) := by
    funext k
    simp only [conv, sum_mul]
    apply sum_congr rfl
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (mem_range.1 hj)
    have : z ^ k = z ^ j * z ^ (k - j) := by rw [← pow_add, Nat.add_sub_cancel' hjk]
    rw [this]; ring
  rw [heq]
  refine ⟨?_, (tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hna hnb).symm⟩
  exact (summable_norm_sum_mul_range_of_summable_norm hna hnb).of_norm

lemma pgf_sumLaw (z : ℝ) (hz : 0 ≤ z) : ∀ (n : ℕ) (ps : Fin n → ℕ → ℝ), (∀ i k, 0 ≤ ps i k) →
    (∀ i, Summable fun k => ps i k * z ^ k) →
    Summable (fun k => sumLaw n ps k * z ^ k) ∧
      ∑' k, sumLaw n ps k * z ^ k = ∏ i, ∑' k, ps i k * z ^ k
  | 0, ps, _, _ => by
    have e : (fun k => sumLaw 0 ps k * z ^ k) = fun k => if k = 0 then 1 else 0 := by
      funext k; simp only [sumLaw]; split_ifs with h <;> simp [h]
    rw [e]
    refine ⟨summable_of_ne_finset_zero (s := {0}) (by intro k hk; simp at hk; simp [hk]), ?_⟩
    rw [tsum_ite_eq]; simp
  | n + 1, ps, h0, hs => by
    obtain ⟨ih1, ih2⟩ := pgf_sumLaw z hz n (fun i => ps i.castSucc) (fun i k => h0 _ k)
      (fun i => hs _)
    simp only [sumLaw]
    obtain ⟨c1, c2⟩ := pgf_conv _ _ (sumLaw_nonneg n _ fun i k => h0 _ k) (h0 _) z hz ih1
      (hs (Fin.last n))
    refine ⟨c1, ?_⟩
    rw [c2, ih2, Fin.prod_univ_castSucc]

lemma pmfMean_nonneg (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) : 0 ≤ pmfMean p :=
  tsum_nonneg fun k => mul_nonneg (Nat.cast_nonneg _) (hp k)

/-- `-ln(1-x) ≤ (x/y)(-ln(1-y))` for `0 ≤ x ≤ y < 1`, i.e. `(x/y) ln(1-y) ≤ ln(1-x)`. -/
lemma log_chord (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y < 1) (hy0 : 0 < y) :
    x / y * Real.log (1 - y) ≤ Real.log (1 - x) := by
  have hc := (strictConcaveOn_log_Ioi).concaveOn
  have h1 : (1 - y) ∈ Set.Ioi (0 : ℝ) := by simp; linarith
  have h2 : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := by simp
  have ha : 0 ≤ x / y := div_nonneg hx hy0.le
  have hb : 0 ≤ 1 - x / y := by rw [sub_nonneg, div_le_one hy0]; exact hxy
  have := hc.2 h1 h2 ha hb (by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero] at this
  have e : x / y * (1 - y) + (1 - x / y) * 1 = 1 - x := by field_simp; ring
  rwa [e] at this

end HubSpokeA12Aux

open HubSpokePricing.Lagrangian Finset HubSpokeA12Aux

theorem solution (n : ℕ) (ps : Fin n → ℕ → ℝ) (hlc : ∀ i, IsLogConcave (ps i))
    (c : ℝ) (hc : 0 < c) (hmean : ∀ i, pmfMean (ps i) ≤ c) (lam : ℝ) (hlam : 1 ≤ lam) :
    ∑' k : ℕ, (if lam * (∑ i, pmfMean (ps i)) ≤ (k : ℝ) then sumLaw n ps k else 0) ≤
      Real.exp (-((lam - 1) * (∑ i, pmfMean (ps i))) / (1 + c) -
        ((n : ℝ) + ∑ i, pmfMean (ps i)) / (1 + c) *
          Real.log (1 - (lam * (∑ i, pmfMean (ps i)) - ∑ i, pmfMean (ps i)) /
            (lam * (∑ i, pmfMean (ps i)) + n))) := by
  set μi : Fin n → ℝ := fun i => pmfMean (ps i) with hμi
  set μ : ℝ := ∑ i, μi i with hμ
  have hps0 : ∀ i k, 0 ≤ ps i k := fun i k => (hlc i).1 k
  have hμi0 : ∀ i, 0 ≤ μi i := fun i => pmfMean_nonneg _ (hps0 i)
  have hμ0 : 0 ≤ μ := sum_nonneg fun i _ => hμi0 i
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set D : ℝ := lam * μ + n with hD
  have hD0 : 0 ≤ D := by nlinarith
  set t : ℝ := (lam - 1) * μ / ((1 + c) * D) with ht
  have ht0 : 0 ≤ t := by
    apply div_nonneg (mul_nonneg (by linarith) hμ0) (mul_nonneg (by linarith) hD0)
  -- (1+c) t = (lam μ - μ)/D
  have hyt : (1 + c) * t = (lam * μ - μ) / D := by
    rw [ht]
    rcases hD0.lt_or_eq with hDp | hDz
    · field_simp
    · rw [← hDz]; simp
  have hy1 : (1 + c) * t < 1 := by
    rw [hyt]
    rcases hD0.lt_or_eq with hDp | hDz
    · rw [div_lt_one hDp]; nlinarith
    · rw [← hDz]; simp
  -- each factor
  set z : ℝ := Real.exp t with hz
  have hz1 : 1 ≤ z := Real.one_le_exp ht0
  have hxi : ∀ i, (1 + μi i) * t ≤ (1 + c) * t := fun i =>
    mul_le_mul_of_nonneg_right (by linarith [hmean i]) ht0
  have hfac : ∀ i, Summable (fun k => ps i k * z ^ k) ∧
      ∑' k, ps i k * z ^ k ≤ Real.exp (-t) / (1 - (1 + μi i) * t) := by
    intro i
    have hpos : 0 < 1 - (1 + μi i) * t := by linarith [hxi i]
    have hexp : 1 - t ≤ Real.exp (-t) := by linarith [Real.add_one_le_exp (-t)]
    -- (1+μ)e^{-t} - μ ≥ 1 - (1+μ) t > 0
    have hq : 1 - (1 + μi i) * t ≤ (1 + μi i) * Real.exp (-t) - μi i := by
      have := mul_le_mul_of_nonneg_left hexp (by linarith [hμi0 i] : (0:ℝ) ≤ 1 + μi i)
      linarith
    have hzexp : z * Real.exp (-t) = 1 := by rw [hz, ← Real.exp_add]; simp
    have hcond : μi i * (z - 1) < 1 := by
      have : 0 < (1 + μi i) * Real.exp (-t) - μi i := lt_of_lt_of_le hpos hq
      have hzp : 0 < z := Real.exp_pos t
      have := mul_pos hzp this
      have e : z * ((1 + μi i) * Real.exp (-t) - μi i) = (1 + μi i) - μi i * z := by
        linear_combination (1 + μi i) * hzexp
      linarith
    obtain ⟨hs, hb⟩ := lemma_A_14 (ps i) (hlc i) z hz1 hcond
    refine ⟨hs, hb.trans ?_⟩
    have hden : 0 < 1 - μi i * (z - 1) := by linarith
    rw [div_le_div_iff₀ hden hpos, one_mul]
    -- 1 - (1+μ)t ≤ e^{-t} (1 - μ(z-1)) = (1+μ)e^{-t} - μ
    have : Real.exp (-t) * (1 - μi i * (z - 1)) = (1 + μi i) * Real.exp (-t) - μi i := by
      have : Real.exp (-t) * z = 1 := by rw [mul_comm]; exact hzexp
      linear_combination (-μi i) * this
    linarith
  obtain ⟨hsum, hpgf⟩ := pgf_sumLaw z (by linarith) n ps hps0 (fun i => (hfac i).1)
  -- Chernoff
  have hcher : ∑' k : ℕ, (if lam * μ ≤ (k : ℝ) then sumLaw n ps k else 0) ≤
      Real.exp (-(t * (lam * μ))) * ∑' k, sumLaw n ps k * z ^ k := by
    rw [← tsum_mul_left]
    have hle : ∀ k : ℕ, (if lam * μ ≤ (k : ℝ) then sumLaw n ps k else 0) ≤
        Real.exp (-(t * (lam * μ))) * (sumLaw n ps k * z ^ k) := by
      intro k
      have h0 := sumLaw_nonneg n ps hps0 k
      split_ifs with hk
      · have : Real.exp (-(t * (lam * μ))) * z ^ k = Real.exp (t * (k - lam * μ)) := by
          rw [hz, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
        have h1 : 1 ≤ Real.exp (t * (k - lam * μ)) :=
          Real.one_le_exp (mul_nonneg ht0 (by linarith))
        calc sumLaw n ps k = sumLaw n ps k * 1 := by ring
          _ ≤ sumLaw n ps k * Real.exp (t * (k - lam * μ)) := mul_le_mul_of_nonneg_left h1 h0
          _ = _ := by rw [← this]; ring
      · exact mul_nonneg (Real.exp_pos _).le (mul_nonneg h0 (pow_nonneg (by linarith) k))
    have hs' : Summable fun k : ℕ => Real.exp (-(t * (lam * μ))) * (sumLaw n ps k * z ^ k) :=
      hsum.mul_left _
    refine Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le (fun k => ?_) hle hs') hs'
    split_ifs
    · exact sumLaw_nonneg n ps hps0 k
    · exact le_rfl
  -- product bound
  have hprod : ∏ i, ∑' k, ps i k * z ^ k ≤ ∏ i, Real.exp (-t) / (1 - (1 + μi i) * t) :=
    prod_le_prod (fun i _ => tsum_nonneg fun k => mul_nonneg (hps0 i k)
      (pow_nonneg (by linarith) k)) (fun i _ => (hfac i).2)
  have hfac_exp : ∀ i, Real.exp (-t) / (1 - (1 + μi i) * t) =
      Real.exp (-t - Real.log (1 - (1 + μi i) * t)) := by
    intro i
    have hpos : 0 < 1 - (1 + μi i) * t := by linarith [hxi i]
    rw [Real.exp_sub, Real.exp_log hpos]
  have hlogb : ∀ i, -t - Real.log (1 - (1 + μi i) * t) ≤
      -t - (1 + μi i) / (1 + c) * Real.log (1 - (1 + c) * t) := by
    intro i
    rcases ht0.lt_or_eq with htp | htz
    · have := log_chord ((1 + μi i) * t) ((1 + c) * t) (by nlinarith [hμi0 i]) (hxi i) hy1
        (by nlinarith)
      have e : (1 + μi i) * t / ((1 + c) * t) = (1 + μi i) / (1 + c) := by
        field_simp
      rw [e] at this
      linarith
    · rw [← htz]; simp
  have hsumexp : ∏ i, Real.exp (-t) / (1 - (1 + μi i) * t) ≤
      Real.exp (-(t * n) - (n + μ) / (1 + c) * Real.log (1 - (1 + c) * t)) := by
    simp_rw [hfac_exp]
    rw [← Real.exp_sum]
    apply Real.exp_le_exp.2
    calc ∑ i, (-t - Real.log (1 - (1 + μi i) * t))
        ≤ ∑ i, (-t - (1 + μi i) / (1 + c) * Real.log (1 - (1 + c) * t)) :=
          sum_le_sum fun i _ => hlogb i
      _ = -(t * n) - (n + μ) / (1 + c) * Real.log (1 - (1 + c) * t) := by
          rw [sum_sub_distrib, ← sum_mul, ← sum_div, sum_add_distrib]
          simp [hμ]; ring
  calc _ ≤ Real.exp (-(t * (lam * μ))) * ∑' k, sumLaw n ps k * z ^ k := hcher
    _ ≤ Real.exp (-(t * (lam * μ))) *
          Real.exp (-(t * n) - (n + μ) / (1 + c) * Real.log (1 - (1 + c) * t)) := by
        rw [hpgf]
        exact mul_le_mul_of_nonneg_left (hprod.trans hsumexp) (Real.exp_pos _).le
    _ = _ := by
        rw [← Real.exp_add, hyt]
        congr 1
        have htD : t * D = (lam - 1) * μ / (1 + c) := by
          rw [ht]
          rcases hD0.lt_or_eq with hDp | hDz
          · field_simp
          · rw [← hDz]
            have hμz : μ = 0 := by nlinarith
            simp [hμz]
        have : -(t * (lam * μ)) + (-(t * n)) = -(t * D) := by rw [hD]; ring
        linear_combination this - htD
