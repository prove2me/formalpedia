-- Prove2me | solution 1 for LindelofHypothesis.mu_eq_zero_of_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-13T02:35:28.518533+00:00
-- url     : https://prove2.me/submissions/6f6ff308-5837-4559-9ed8-d0af2072e051

import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts

set_option autoImplicit false
open Complex Filter Asymptotics
open scoped ENNReal

/-!
# `μ(σ) = 0` for `σ > 1`

Helper namespace `LindelofHypothesis.LHA`.  Shared, standalone lemmas (copy freely):

* `LHA.mu_le_of_isBigO`      (M1)  `ζ(σ+iT) = O(T^a) → mu σ ≤ a`
* `LHA.isBigO_of_mu_lt`      (M2)  `mu σ < a → ζ(σ+iT) = O(T^a)`
* `LHA.nonneg_of_isBigO_of_norm_ge`  `‖f T‖ ≥ c > 0` eventually and `f = O(T^a)` → `0 ≤ a`
* `LHA.zero_le_mu_of_norm_ge` (M3)  `‖ζ(σ+iT)‖ ≥ c > 0` eventually → `0 ≤ mu σ`
* `LHA.norm_riemannZeta_le_tsum`   `σ > 1, Re s ≥ σ → ‖ζ s‖ ≤ ∑ ‖term 1 σ n‖ (= ∑ n^{-σ})`
* `LHA.inv_tsum_le_norm_riemannZeta`  `σ > 1, Re s ≥ σ → 0 < B(σ) ∧ B(σ)⁻¹ ≤ ‖ζ s‖`
  (via `ζ(s) · L(μ, s) = 1` and `‖L(μ, s)‖ ≤ B(σ)`)
* `LHA.exists_norm_riemannZeta_le`   `σ > 1 → ∃ C, ∀ s, σ ≤ Re s → ‖ζ s‖ ≤ C`
* `LHA.exists_pos_le_norm_riemannZeta` `σ > 1 → ∃ c > 0, ∀ s, σ ≤ Re s → c ≤ ‖ζ s‖`
-/

namespace LindelofHypothesis.LHA

open LSeries

/-! ## Bounds for `ζ` on half-planes `Re s ≥ σ > 1` -/

lemma summable_norm_term_one {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => ‖LSeries.term 1 (σ : ℂ) n‖) :=
  summable_norm_iff.mpr (LSeriesSummable_one_iff.mpr (by simpa using hσ))

/-- An L-series with coefficients of norm `≤ 1` is bounded by `∑ n^{-σ}` on `Re s ≥ σ > 1`. -/
lemma norm_LSeries_le_of_norm_le_one {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ)
    {s : ℂ} (hs : σ ≤ s.re) :
    ‖LSeries f s‖ ≤ ∑' n : ℕ, ‖LSeries.term 1 (σ : ℂ) n‖ := by
  have hpt : ∀ n : ℕ, ‖LSeries.term f s n‖ ≤ ‖LSeries.term 1 (σ : ℂ) n‖ := by
    intro n
    calc ‖LSeries.term f s n‖ ≤ ‖LSeries.term 1 s n‖ :=
          LSeries.norm_term_le s (by simpa using hf n)
      _ ≤ ‖LSeries.term 1 (σ : ℂ) n‖ :=
          LSeries.norm_term_le_of_re_le_re 1 (by simpa using hs) n
  have hsum : Summable (fun n : ℕ => ‖LSeries.term f s n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt (summable_norm_term_one hσ)
  calc ‖LSeries f s‖ = ‖∑' n, LSeries.term f s n‖ := rfl
    _ ≤ ∑' n, ‖LSeries.term f s n‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' n : ℕ, ‖LSeries.term 1 (σ : ℂ) n‖ :=
        Summable.tsum_le_tsum hpt hsum (summable_norm_term_one hσ)

/-- Upper bound: `‖ζ(s)‖ ≤ ∑ n^{-σ}` for `Re s ≥ σ > 1`. -/
lemma norm_riemannZeta_le_tsum {σ : ℝ} (hσ : 1 < σ) {s : ℂ} (hs : σ ≤ s.re) :
    ‖riemannZeta s‖ ≤ ∑' n : ℕ, ‖LSeries.term 1 (σ : ℂ) n‖ := by
  rw [← LSeries_one_eq_riemannZeta (by linarith)]
  exact norm_LSeries_le_of_norm_le_one (fun n => by simp) hσ hs

open scoped LSeries.notation in
open ArithmeticFunction in
open scoped ArithmeticFunction.Moebius in
/-- Lower bound: `‖ζ(s)‖ ≥ (∑ n^{-σ})⁻¹ > 0` for `Re s ≥ σ > 1`, from `ζ(s) · L(μ, s) = 1`. -/
lemma inv_tsum_le_norm_riemannZeta {σ : ℝ} (hσ : 1 < σ) {s : ℂ} (hs : σ ≤ s.re) :
    0 < ∑' n : ℕ, ‖LSeries.term 1 (σ : ℂ) n‖ ∧
    (∑' n : ℕ, ‖LSeries.term 1 (σ : ℂ) n‖)⁻¹ ≤ ‖riemannZeta s‖ := by
  have hs' : 1 < s.re := by linarith
  have h1 := LSeries_one_mul_Lseries_moebius hs'
  rw [LSeries_one_eq_riemannZeta hs'] at h1
  have hμ : ‖L ↗μ s‖ ≤ ∑' n : ℕ, ‖LSeries.term 1 (σ : ℂ) n‖ := by
    refine norm_LSeries_le_of_norm_le_one (fun n => ?_) hσ hs
    have := abs_moebius_le_one (n := n)
    simp only [Complex.norm_intCast]
    exact_mod_cast this
  have hprod : ‖riemannZeta s‖ * ‖L ↗μ s‖ = 1 := by rw [← norm_mul, h1, norm_one]
  have hpos : 0 < ‖L ↗μ s‖ := by
    rcases (norm_nonneg (L ↗μ s)).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hprod; exact absurd hprod zero_ne_one
  refine ⟨hpos.trans_le hμ, ?_⟩
  calc (∑' n : ℕ, ‖LSeries.term 1 (σ : ℂ) n‖)⁻¹ ≤ ‖L ↗μ s‖⁻¹ := inv_anti₀ hpos hμ
    _ = ‖riemannZeta s‖ := inv_eq_of_mul_eq_one_left hprod

/-- Uniform upper bound for `ζ` on `Re s ≥ σ > 1`. -/
lemma exists_norm_riemannZeta_le {σ : ℝ} (hσ : 1 < σ) :
    ∃ C : ℝ, ∀ s : ℂ, σ ≤ s.re → ‖riemannZeta s‖ ≤ C :=
  ⟨_, fun _ hs => norm_riemannZeta_le_tsum hσ hs⟩

/-- Uniform positive lower bound for `ζ` on `Re s ≥ σ > 1`: `‖ζ(s)‖ ≥ c(σ) > 0`. -/
lemma exists_pos_le_norm_riemannZeta {σ : ℝ} (hσ : 1 < σ) :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, σ ≤ s.re → c ≤ ‖riemannZeta s‖ := by
  have hB := (inv_tsum_le_norm_riemannZeta hσ (s := (σ : ℂ)) (by simp)).1
  exact ⟨_, inv_pos.mpr hB, fun _ hs => (inv_tsum_le_norm_riemannZeta hσ hs).2⟩

/-- Lower bound on a vertical line `Re s = σ > 1`. -/
lemma exists_pos_le_norm_riemannZeta_line {σ : ℝ} (hσ : 1 < σ) :
    ∃ c : ℝ, 0 < c ∧ ∀ T : ℝ, c ≤ ‖riemannZeta (σ + T * I)‖ := by
  obtain ⟨c, hc, h⟩ := exists_pos_le_norm_riemannZeta hσ
  exact ⟨c, hc, fun T => h _ (by simp)⟩

/-! ## Shared lemmas about `mu` -/

/-- (M1) If `ζ(σ+iT) = O(T^a)` then `mu σ ≤ a`. -/
theorem mu_le_of_isBigO {σ a : ℝ}
    (h : (fun T : ℝ => riemannZeta (σ + T * I)) =O[atTop] (fun T : ℝ => T ^ a)) :
    mu σ ≤ (a : EReal) :=
  sInf_le ⟨a, h, rfl⟩

/-- `T^b = O(T^a)` at `+∞` when `b ≤ a`. -/
lemma rpow_isBigO_rpow_of_le {a b : ℝ} (hab : b ≤ a) :
    (fun T : ℝ => T ^ b) =O[atTop] (fun T : ℝ => T ^ a) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 1] with T hT
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _),
    abs_of_nonneg (Real.rpow_nonneg (by linarith) _), one_mul]
  exact Real.rpow_le_rpow_of_exponent_le hT hab

/-- (M2) If `mu σ < a` (with `a` real) then `ζ(σ+iT) = O(T^a)`. -/
theorem isBigO_of_mu_lt {σ a : ℝ} (h : mu σ < (a : EReal)) :
    (fun T : ℝ => riemannZeta (σ + T * I)) =O[atTop] (fun T : ℝ => T ^ a) := by
  obtain ⟨b, ⟨a', ha', rfl⟩, hlt⟩ := sInf_lt_iff.mp h
  exact ha'.trans (rpow_isBigO_rpow_of_le (EReal.coe_lt_coe_iff.mp hlt).le)

/-- If `‖f T‖ ≥ c > 0` eventually and `f = O(T^a)` at `+∞`, then `0 ≤ a`. -/
lemma nonneg_of_isBigO_of_norm_ge {f : ℝ → ℂ} {a c : ℝ} (hc : 0 < c)
    (hlow : ∀ᶠ T in atTop, c ≤ ‖f T‖) (h : f =O[atTop] (fun T : ℝ => T ^ a)) : 0 ≤ a := by
  by_contra ha'
  have ha : a < 0 := not_le.mp ha'
  have ht : Tendsto (fun T : ℝ => T ^ a) atTop (nhds 0) := by
    simpa using tendsto_rpow_neg_atTop (y := -a) (by linarith)
  have hf : Tendsto f atTop (nhds 0) := h.trans_tendsto ht
  have hfn : ∀ᶠ T in atTop, ‖f T‖ < c := by
    have := hf.norm
    rw [norm_zero] at this
    exact (tendsto_order.1 this).2 c hc
  obtain ⟨T, h1, h2⟩ := (hlow.and hfn).exists
  exact absurd (h1.trans_lt h2) (lt_irrefl _)

/-- (M3) If `‖ζ(σ+iT)‖ ≥ c > 0` eventually, then `0 ≤ mu σ`. -/
theorem zero_le_mu_of_norm_ge {σ c : ℝ} (hc : 0 < c)
    (h : ∀ᶠ T : ℝ in atTop, c ≤ ‖riemannZeta (σ + T * I)‖) : 0 ≤ mu σ := by
  refine le_sInf ?_
  rintro _ ⟨a, ha, rfl⟩
  exact EReal.coe_nonneg.mpr (nonneg_of_isBigO_of_norm_ge hc h ha)

/-! ## Target 1 -/

/-- `ζ(σ+iT) = O(1) = O(T^0)` for `σ > 1`. -/
lemma isBigO_rpow_zero_of_one_lt {σ : ℝ} (hσ : 1 < σ) :
    (fun T : ℝ => riemannZeta (σ + T * I)) =O[atTop] (fun T : ℝ => T ^ (0 : ℝ)) := by
  refine IsBigO.of_bound (∑' n : ℕ, ‖LSeries.term 1 (σ : ℂ) n‖) ?_
  filter_upwards with T
  rw [Real.rpow_zero, norm_one, mul_one]
  exact norm_riemannZeta_le_tsum hσ (by simp)

/-- `mu σ ≤ 0` for `σ > 1`. -/
theorem mu_le_zero_of_one_lt {σ : ℝ} (hσ : 1 < σ) : mu σ ≤ 0 := by
  simpa using mu_le_of_isBigO (isBigO_rpow_zero_of_one_lt hσ)

/-- `0 ≤ mu σ` for `σ > 1`. -/
theorem zero_le_mu_of_one_lt {σ : ℝ} (hσ : 1 < σ) : 0 ≤ mu σ := by
  obtain ⟨c, hc, h⟩ := exists_pos_le_norm_riemannZeta_line hσ
  exact zero_le_mu_of_norm_ge hc (Eventually.of_forall h)

theorem mu_eq_zero_of_one_lt (σ : ℝ) (hσ : 1 < σ) : mu σ = 0 :=
  le_antisymm (mu_le_zero_of_one_lt hσ) (zero_le_mu_of_one_lt hσ)

end LindelofHypothesis.LHA

open LindelofHypothesis in
theorem solution (σ : ℝ) (hσ : 1 < σ) : mu σ = 0 :=
  LHA.mu_eq_zero_of_one_lt σ hσ
