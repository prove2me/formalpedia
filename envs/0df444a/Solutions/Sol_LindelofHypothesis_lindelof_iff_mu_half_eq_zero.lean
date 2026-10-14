-- Prove2me | solution 1 for LindelofHypothesis.lindelof_iff_mu_half_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-13T02:39:48.283782+00:00
-- url     : https://prove2.me/submissions/cd44c03f-c052-4557-afee-ea578afef9a9

import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts

set_option autoImplicit false
open Complex Filter Asymptotics
open scoped ENNReal

/-!
# Lindelöf hypothesis `⇔ μ(1/2) = 0`

Helper namespace `LindelofHypothesis.LHC`.  Does NOT import the Phragmén–Lindelöf platform
theorem: the weighted Phragmén–Lindelöf argument is reduced to Mathlib's
`PhragmenLindelof.vertical_strip`, so every lemma is axiom-clean.

Reusable lemmas (copy freely):

* (copied from target 1, `LHA`) bounds for `ζ` on `Re s ≥ σ > 1`, (M1) `mu_le_of_isBigO`,
  (M2) `isBigO_of_mu_lt`, (M3) `zero_le_mu_of_norm_ge`, `nonneg_of_isBigO_of_norm_ge`.
* A-priori bound in `Re s > 0` (via `ζ₁(s) = s + s(s-1) ∫_1^∞ (⌊t⌋-t) t^{-s-1} dt`):
  - `norm_riemannZeta₁_le (hs : 0 < s.re) : ‖riemannZeta₁ s‖ ≤ ‖s‖ + ‖s‖ * ‖s - 1‖ / s.re`
  - `norm_riemannZeta_le_of_re_pos (hs : 0 < s.re) (hs1 : s ≠ 1) :
       ‖riemannZeta s‖ ≤ ‖s‖ / ‖s - 1‖ + ‖s‖ / s.re`
  (`riemannZeta₁` is Mathlib's entire function `(s-1) ζ(s)` completed at `s = 1`.)
* Phragmén–Lindelöf with different exponents (auxiliary weight `(-i(s-c))^{-(p+qs)}`):
  - `pl_interp`: polynomial a-priori bound on the closed strip `a ≤ Re ≤ b`, bounds
    `M (1+|t|)^α` on `Re = a` and `M (1+|t|)^β` on `Re = b` (all real `t`) give, for each
    `σ ∈ [a,b]`, `‖f(σ+it)‖ ≤ C (1+t)^{((b-σ)α+(σ-a)β)/(b-a)}` for `t ≥ 0`.
  - `norm_riemannZeta₁_le_poly (h0 : 0 < σ₀) z (σ₀ ≤ z.re) (z.re ≤ σ₁) :
       ‖riemannZeta₁ z‖ ≤ ((|σ₁|+1) + (|σ₁|+1)^2/σ₀) * (1 + |z.im|) ^ (2:ℝ)`
* Symmetry / global bounds: `riemannZeta₁_conj`, `norm_riemannZeta_neg_im`,
  `norm_riemannZeta₁_neg_im`, `exists_global_bound` (big-O at `+∞` + continuity + symmetry
  ⇒ `‖g t‖ ≤ M (1+|t|)^e` for all `t`).
-/

namespace LindelofHypothesis.LHC

open Set MeasureTheory LSeries

/-! ## Copied from target 1 (`LHA`): bounds on `Re s > 1` and (M1)–(M3) -/



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




/-! ## A priori bound for `ζ` in `Re s > 0` -/

lemma norm_floor_sub_le {t : ℝ} (ht : 0 ≤ t) : ‖((⌊t⌋₊ : ℂ) - t)‖ ≤ 1 := by
  have h1 : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht
  have h2 : t < ⌊t⌋₊ + 1 := Nat.lt_floor_add_one t
  have : ((⌊t⌋₊ : ℂ) - t) = (((⌊t⌋₊ : ℝ) - t : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-- The sawtooth `⌊t⌋ - t` on `t > 1`, extended by zero. -/
noncomputable def saw (t : ℝ) : ℂ := Set.indicator (Ioi (1:ℝ)) (fun t : ℝ => ((⌊t⌋₊ : ℂ) - t)) t

lemma norm_saw_le (t : ℝ) : ‖saw t‖ ≤ 1 := by
  unfold saw
  by_cases ht : t ∈ Ioi (1:ℝ)
  · rw [indicator_of_mem ht]
    exact norm_floor_sub_le (le_of_lt (lt_trans zero_lt_one ht))
  · rw [indicator_of_notMem ht]; simp

lemma measurable_floor_sub : Measurable (fun t : ℝ => ((⌊t⌋₊ : ℂ) - t)) := by
  fun_prop

lemma measurable_saw : Measurable saw :=
  measurable_floor_sub.indicator measurableSet_Ioi

/-- `J s = ∫_{1}^{∞} (⌊t⌋ - t) t^{-s-1} dt`, as a Mellin transform. -/
noncomputable def J (s : ℂ) : ℂ := mellin saw (-s)

lemma J_eq (s : ℂ) :
    J s = ∫ t in Ioi (1:ℝ), ((⌊t⌋₊ : ℂ) - t) * (t : ℂ) ^ (-(s + 1)) := by
  unfold J mellin saw
  have : ∀ t : ℝ, (t : ℂ) ^ (-s - 1) • (Ioi (1:ℝ)).indicator (fun t : ℝ => ((⌊t⌋₊ : ℂ) - t)) t
      = (Ioi (1:ℝ)).indicator (fun t : ℝ => ((⌊t⌋₊ : ℂ) - t) * (t : ℂ) ^ (-(s + 1))) t := by
    intro t
    by_cases ht : t ∈ Ioi (1:ℝ)
    · rw [indicator_of_mem ht, indicator_of_mem ht, smul_eq_mul, mul_comm]
      congr 2; ring
    · rw [indicator_of_notMem ht, indicator_of_notMem ht, smul_zero]
  simp_rw [this]
  rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right zero_le_one]

lemma differentiableAt_J {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ J s := by
  have h : DifferentiableAt ℂ (mellin saw) (-s) := by
    refine mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := -s.re - 1) ?_ ?_ ?_ ?_ ?_
    · refine (locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed).mpr fun K _ hK => ?_
      exact IntegrableOn.of_bound hK.measure_lt_top measurable_saw.aestronglyMeasurable 1
        (ae_of_all _ norm_saw_le)
    · refine IsBigO.of_bound 1 (Eventually.of_forall fun t => ?_)
      simp only [neg_zero, Real.rpow_zero, norm_one, mul_one]
      exact norm_saw_le t
    · simp [hs]
    · refine IsBigO.of_bound 0 ?_
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds zero_lt_one)]
        with t ht
      have : saw t = 0 := by
        unfold saw
        exact indicator_of_notMem (by simp; linarith) _
      simp [this]
    · simp
  exact h.comp s differentiableAt_id.neg

lemma integrableOn_floor_sub_mul {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => ((⌊t⌋₊ : ℂ) - t) * (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  have hint : IntegrableOn (fun t : ℝ => t ^ (-(s.re + 1))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  refine hint.mono' ?_ ?_
  · refine (Measurable.aestronglyMeasurable ?_)
    exact measurable_floor_sub.mul (by fun_prop)
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht0 : (0:ℝ) < t := lt_trans zero_lt_one ht
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0]
    have : (-(s + 1)).re = -(s.re + 1) := by simp
    rw [this]
    calc ‖((⌊t⌋₊ : ℂ) - t)‖ * t ^ (-(s.re + 1)) ≤ 1 * t ^ (-(s.re + 1)) :=
          mul_le_mul_of_nonneg_right (norm_floor_sub_le ht0.le) (Real.rpow_nonneg ht0.le _)
      _ = t ^ (-(s.re + 1)) := one_mul _

lemma norm_J_le {s : ℂ} (hs : 0 < s.re) : ‖J s‖ ≤ 1 / s.re := by
  rw [J_eq]
  have hint : IntegrableOn (fun t : ℝ => t ^ (-(s.re + 1))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  calc ‖∫ t in Ioi (1:ℝ), ((⌊t⌋₊ : ℂ) - t) * (t : ℂ) ^ (-(s + 1))‖
      ≤ ∫ t in Ioi (1:ℝ), t ^ (-(s.re + 1)) := by
        refine norm_integral_le_of_norm_le hint
          (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
        have ht0 : (0:ℝ) < t := lt_trans zero_lt_one ht
        rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0]
        have : (-(s + 1)).re = -(s.re + 1) := by simp
        rw [this]
        calc ‖((⌊t⌋₊ : ℂ) - t)‖ * t ^ (-(s.re + 1)) ≤ 1 * t ^ (-(s.re + 1)) :=
              mul_le_mul_of_nonneg_right (norm_floor_sub_le ht0.le) (Real.rpow_nonneg ht0.le _)
          _ = t ^ (-(s.re + 1)) := one_mul _
    _ = 1 / s.re := by
        rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
        have : -(s.re + 1) + 1 = -s.re := by ring
        rw [this]
        field_simp

/-- For `Re s > 1`: `ζ(s) = s/(s-1) + s J(s)`. -/
lemma riemannZeta_eq_of_one_lt {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s / (s - 1) + s * J s := by
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ‖(1 : ℕ → ℂ) k‖) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (1:ℝ) := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
    simp
  have h1 := LSeries_eq_mul_integral' (1 : ℕ → ℂ) zero_le_one (by simpa using hs) hO
  rw [LSeries_one_eq_riemannZeta hs] at h1
  rw [h1]
  have hs0 : 0 < s.re := by linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h; have := congrArg re h; simp at this; linarith
  have hfl : ∀ t : ℝ, (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℕ → ℂ) k) = (⌊t⌋₊ : ℂ) := by
    intro t; simp
  simp_rw [hfl]
  have hcpow : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one
  have hsplit : ∫ t in Ioi (1:ℝ), (⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1)) =
      (∫ t in Ioi (1:ℝ), ((⌊t⌋₊ : ℂ) - t) * (t : ℂ) ^ (-(s + 1))) +
        ∫ t in Ioi (1:ℝ), (t : ℂ) ^ (-s) := by
    rw [← integral_add (integrableOn_floor_sub_mul hs0) hcpow]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (lt_trans zero_lt_one ht).ne'
    have : (t : ℂ) ^ (-s) = (t : ℂ) ^ (-(s + 1)) * t := by
      have e : -s = -(s + 1) + 1 := by ring
      rw [e, cpow_add _ _ ht0, cpow_one]
    rw [this]; ring
  rw [hsplit, ← J_eq, integral_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one]
  simp only [ofReal_one, one_cpow]
  have : -s + 1 = -(s - 1) := by ring
  rw [this]
  field_simp
  ring

lemma riemannZeta₁_eq_mul {s : ℂ} (hs : s ≠ 1) : riemannZeta₁ s = (s - 1) * riemannZeta s := by
  have h1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [riemannZeta_eq_inv_sub_mul hs, ← mul_assoc, mul_inv_cancel₀ h1, one_mul]

/-- The entire function `riemannZeta₁ = (s-1) ζ(s)` satisfies `ζ₁(s) = s + s(s-1)J(s)` on `Re s > 0`. -/
lemma riemannZeta₁_eq {s : ℂ} (hs : 0 < s.re) : riemannZeta₁ s = s + s * (s - 1) * J s := by
  let U : Set ℂ := {z | 0 < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have h1 : AnalyticOnNhd ℂ riemannZeta₁ U :=
    differentiable_riemannZeta₁.differentiableOn.analyticOnNhd hU
  have h2 : AnalyticOnNhd ℂ (fun z => z + z * (z - 1) * J z) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hU
    have := differentiableAt_J (s := z) hz
    exact (differentiableAt_id.add ((differentiableAt_id.mul
      (differentiableAt_id.sub_const 1)).mul this)).differentiableWithinAt
  have heq := h1.eqOn_of_preconnected_of_eventuallyEq h2 hUc (show (2:ℂ) ∈ U by simp [U])
    (eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_re).mem_nhds
      (show (1:ℝ) < (2:ℂ).re by norm_num)) fun z hz => ?_)
  · exact heq hs
  · have hz : 1 < z.re := hz
    have hz1 : z ≠ 1 := by intro h; rw [h] at hz; simp at hz
    have h1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
    rw [riemannZeta₁_eq_mul hz1, riemannZeta_eq_of_one_lt hz]
    field_simp

/-- A priori bound for the entire function `ζ₁(s) = (s-1)ζ(s)` on `Re s > 0`. -/
theorem norm_riemannZeta₁_le {s : ℂ} (hs : 0 < s.re) :
    ‖riemannZeta₁ s‖ ≤ ‖s‖ + ‖s‖ * ‖s - 1‖ / s.re := by
  rw [riemannZeta₁_eq hs]
  calc ‖s + s * (s - 1) * J s‖ ≤ ‖s‖ + ‖s * (s - 1) * J s‖ := norm_add_le _ _
    _ = ‖s‖ + ‖s‖ * ‖s - 1‖ * ‖J s‖ := by rw [norm_mul, norm_mul]
    _ ≤ ‖s‖ + ‖s‖ * ‖s - 1‖ * (1 / s.re) := by
        gcongr; exact norm_J_le hs
    _ = ‖s‖ + ‖s‖ * ‖s - 1‖ / s.re := by ring

/-- A priori bound for `ζ` on `Re s > 0`, `s ≠ 1`: `‖ζ(s)‖ ≤ ‖s‖/‖s-1‖ + ‖s‖/Re s`. -/
theorem norm_riemannZeta_le_of_re_pos {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s‖ ≤ ‖s‖ / ‖s - 1‖ + ‖s‖ / s.re := by
  have h1 : 0 < ‖s - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hs1)
  have h := norm_riemannZeta₁_le hs
  rw [riemannZeta₁_eq_mul hs1, norm_mul] at h
  rw [div_add_div _ _ h1.ne' hs.ne', le_div_iff₀ (mul_pos h1 hs)]
  have h' := mul_le_mul_of_nonneg_right h hs.le
  rw [add_mul, div_mul_cancel₀ _ hs.ne'] at h'
  linarith




/-! ## Phragmén–Lindelöf with different exponents on the two boundary lines -/

/-- If `y/2 ≤ x ≤ D y` with `y > 0`, then `x^e ≤ ((1/2)^e + D^e) y^e`. -/
lemma rpow_le_of_le_of_le {x y D e : ℝ} (hy : 0 < y) (h1 : y / 2 ≤ x) (h2 : x ≤ D * y) :
    x ^ e ≤ ((1 / 2) ^ e + D ^ e) * y ^ e := by
  have hx : 0 < x := lt_of_lt_of_le (by linarith) h1
  have hD : 0 < D := by
    by_contra h; push Not at h; nlinarith
  have hxy : x = (x / y) * y := by field_simp
  have hr1 : 1 / 2 ≤ x / y := by rw [le_div_iff₀ hy]; linarith
  have hr2 : x / y ≤ D := by rw [div_le_iff₀ hy]; linarith
  have hr0 : 0 < x / y := div_pos hx hy
  rw [hxy, Real.mul_rpow hr0.le hy.le]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hy.le _)
  rcases le_or_gt 0 e with he | he
  · have := Real.rpow_le_rpow hr0.le hr2 he
    have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2) e
    linarith
  · have := Real.rpow_le_rpow_of_nonpos (by norm_num) hr1 he.le
    have := Real.rpow_nonneg hD.le e
    linarith

/-- Jordan-type bound: if `Re z ≥ 0` then `Re z · |arg z| ≤ (π/2)|Im z|`. -/
lemma re_mul_abs_arg_le {z : ℂ} (hz : 0 ≤ z.re) : z.re * |arg z| ≤ Real.pi / 2 * |z.im| := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simp
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have harg : |arg z| ≤ Real.pi / 2 := abs_arg_le_pi_div_two_iff.mpr hz
  have hsin : 2 / Real.pi * |arg z| ≤ |Real.sin (arg z)| := by
    rcases le_or_gt 0 (arg z) with h | h
    · rw [abs_of_nonneg h]
      have := Real.mul_le_sin h (by rw [abs_of_nonneg h] at harg; exact harg)
      exact this.trans (le_abs_self _)
    · rw [abs_of_neg h]
      have h' : -arg z ≤ Real.pi / 2 := by rw [abs_of_neg h] at harg; exact harg
      have := Real.mul_le_sin (by linarith) h'
      rw [Real.sin_neg] at this
      exact this.trans (neg_le_abs _)
  rw [sin_arg, abs_div, abs_of_pos hn] at hsin
  have hpi : 0 < Real.pi := Real.pi_pos
  have h1 : |arg z| ≤ Real.pi / 2 * (|z.im| / ‖z‖) := by
    have := mul_le_mul_of_nonneg_left hsin (by positivity : (0:ℝ) ≤ Real.pi / 2)
    calc |arg z| = Real.pi / 2 * (2 / Real.pi * |arg z|) := by field_simp
      _ ≤ _ := this
  have hre : z.re ≤ ‖z‖ := re_le_norm z
  calc z.re * |arg z| ≤ z.re * (Real.pi / 2 * (|z.im| / ‖z‖)) :=
        mul_le_mul_of_nonneg_left h1 hz
    _ = Real.pi / 2 * |z.im| * (z.re / ‖z‖) := by ring
    _ ≤ Real.pi / 2 * |z.im| * 1 := by
        gcongr
        rw [div_le_one hn]; exact hre
    _ = Real.pi / 2 * |z.im| := mul_one _

lemma mul_arg_nonneg {z : ℂ} {q : ℝ} (hq : 0 ≤ q * z.im) (hz : z.im ≠ 0) : 0 ≤ q * arg z := by
  rcases lt_or_gt_of_ne hz with h | h
  · have hq' : q ≤ 0 := by
      by_contra hc; push Not at hc; nlinarith
    have : arg z < 0 := arg_neg_iff.mpr h
    nlinarith
  · have hq' : 0 ≤ q := by
      by_contra hc; push Not at hc; nlinarith
    have : 0 ≤ arg z := arg_nonneg_iff.mpr h.le
    positivity

/-- Upper bound for the oscillating factor of the weight. -/
lemma mul_re_mul_arg_le {z : ℂ} {q : ℝ} (hq : 0 ≤ q * z.im) (hz : z.im ≠ 0) :
    q * z.re * arg z ≤ |q| * (Real.pi / 2) * |z.im| := by
  have h0 := mul_arg_nonneg hq hz
  rcases le_or_gt z.re 0 with hre | hre
  · have : q * z.re * arg z = z.re * (q * arg z) := by ring
    rw [this]
    have : z.re * (q * arg z) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hre h0
    have : 0 ≤ |q| * (Real.pi / 2) * |z.im| := by positivity
    linarith
  · have h1 := re_mul_abs_arg_le hre.le
    calc q * z.re * arg z ≤ |q * z.re * arg z| := le_abs_self _
      _ = |q| * (z.re * |arg z|) := by rw [abs_mul, abs_mul, abs_of_pos hre]; ring
      _ ≤ |q| * (Real.pi / 2 * |z.im|) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = |q| * (Real.pi / 2) * |z.im| := by ring

lemma mul_re_mul_arg_nonneg {z : ℂ} {q : ℝ} (hq : 0 ≤ q * z.im) (hz : z.im ≠ 0)
    (hre : 0 ≤ z.re) : 0 ≤ q * z.re * arg z := by
  have h0 := mul_arg_nonneg hq hz
  have : q * z.re * arg z = z.re * (q * arg z) := by ring
  rw [this]; positivity

/-- The auxiliary weight `G(s) = (-i(s-c))^{-(p+qs)}`, with the principal branch. -/
noncomputable def weight (p q c : ℝ) (s : ℂ) : ℂ :=
  cexp (-((p : ℂ) + (q : ℂ) * s) * Complex.log (-I * (s - c)))

lemma neg_I_mul_re (s : ℂ) (c : ℝ) : (-I * (s - c)).re = s.im := by simp

lemma neg_I_mul_im (s : ℂ) (c : ℝ) : (-I * (s - c)).im = c - s.re := by simp

lemma differentiableAt_weight (p q c : ℝ) {s : ℂ} (hs : s.re ≠ c) :
    DifferentiableAt ℂ (weight p q c) s := by
  have hslit : -I * (s - c) ∈ slitPlane := by
    rw [mem_slitPlane_iff]; right
    rw [neg_I_mul_im]; intro h; exact hs (by linarith)
  unfold weight
  have h1 : DifferentiableAt ℂ (fun s : ℂ => -I * (s - c)) s := by fun_prop
  have h2 := h1.clog hslit
  have h3 : DifferentiableAt ℂ (fun s : ℂ => -((p : ℂ) + (q : ℂ) * s)) s := by fun_prop
  exact (h3.mul h2).cexp

lemma norm_weight (p q c : ℝ) {s : ℂ} (hs : s.re ≠ c) :
    ‖weight p q c s‖ =
      ‖s - c‖ ^ (-(p + q * s.re)) * Real.exp (q * s.im * arg (-I * (s - c))) := by
  have hpos : 0 < ‖s - c‖ := by
    refine norm_pos_iff.mpr fun h => hs ?_
    have := congrArg re h; simp at this; linarith
  unfold weight
  rw [Complex.norm_exp, Real.rpow_def_of_pos hpos, ← Real.exp_add]
  congr 1
  have hn : ‖-I * (s - c)‖ = ‖s - c‖ := by simp
  simp only [mul_re, neg_re, add_re, ofReal_re, ofReal_im, neg_im, add_im, mul_im, log_re,
    log_im, hn]
  ring

/-- Core Phragmén–Lindelöf step with an explicit weight `weight p q c`. -/
theorem pl_core {a b : ℝ} (hab : a < b) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (re ⁻¹' Ioo a b))
    {K N : ℝ} (hN : 0 ≤ N)
    (hpoly : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖f z‖ ≤ K * (1 + |z.im|) ^ N)
    {M α β : ℝ} (ha : ∀ t : ℝ, ‖f (a + t * I)‖ ≤ M * (1 + |t|) ^ α)
    (hb : ∀ t : ℝ, ‖f (b + t * I)‖ ≤ M * (1 + |t|) ^ β)
    {p q c : ℝ} (hpa : p + q * a = α) (hpb : p + q * b = β)
    (hc1 : ∀ x, a ≤ x → x ≤ b → 1 ≤ |c - x|) (hc2 : ∀ x, a ≤ x → x ≤ b → |c - x| ≤ b - a + 1)
    (hcq : ∀ x, a ≤ x → x ≤ b → 0 ≤ q * (c - x))
    {σ : ℝ} (hσa : a ≤ σ) (hσb : σ ≤ b) :
    ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → ‖f (σ + t * I)‖ ≤ C * (1 + t) ^ (p + q * σ) := by
  have hba : 0 < b - a := sub_pos.mpr hab
  set D : ℝ := b - a + 1 with hD
  have hD1 : 1 ≤ D := by linarith
  set Λ : ℝ := |q| * (Real.pi / 2) * D with hΛ
  set G := weight p q c with hG
  set H : ℂ → ℂ := fun z => f z * G z with hH
  -- basic facts on the closed strip
  have hne : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → z.re ≠ c := by
    intro z h1 h2 h; have := hc1 z.re h1 h2; rw [h, sub_self, abs_zero] at this; linarith
  have hosc : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → q * z.im * arg (-I * (z - c)) ≤ Λ := by
    intro z h1 h2
    have hq : 0 ≤ q * (-I * (z - c)).im := by rw [neg_I_mul_im]; exact hcq _ h1 h2
    have hz : (-I * (z - c)).im ≠ 0 := by
      rw [neg_I_mul_im]; intro h; exact hne z h1 h2 (by linarith)
    have := mul_re_mul_arg_le hq hz
    rw [neg_I_mul_re, neg_I_mul_im] at this
    calc q * z.im * arg (-I * (z - c)) ≤ |q| * (Real.pi / 2) * |c - z.re| := this
      _ ≤ |q| * (Real.pi / 2) * D := by gcongr; exact hc2 _ h1 h2
  have hosc0 : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → 0 ≤ z.im →
      0 ≤ q * z.im * arg (-I * (z - c)) := by
    intro z h1 h2 h3
    have hq : 0 ≤ q * (-I * (z - c)).im := by rw [neg_I_mul_im]; exact hcq _ h1 h2
    have hz : (-I * (z - c)).im ≠ 0 := by
      rw [neg_I_mul_im]; intro h; exact hne z h1 h2 (by linarith)
    have := mul_re_mul_arg_nonneg hq hz (by rw [neg_I_mul_re]; exact h3)
    rwa [neg_I_mul_re] at this
  have hdist : ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      1 ≤ ‖z - c‖ ∧ (1 + |z.im|) / 2 ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ D * (1 + |z.im|) := by
    intro z h1 h2
    have e1 : |(z - c).re| ≤ ‖z - c‖ := abs_re_le_norm _
    have e2 : |(z - c).im| ≤ ‖z - c‖ := abs_im_le_norm _
    have e3 : ‖z - c‖ ≤ |(z - c).re| + |(z - c).im| := norm_le_abs_re_add_abs_im _
    have hre : (z - c).re = z.re - c := by simp
    have him : (z - c).im = z.im := by simp
    simp only [hre, him] at e1 e2 e3
    have k1 := hc1 _ h1 h2
    have k2 := hc2 _ h1 h2
    rw [abs_sub_comm] at k1 k2
    refine ⟨k1.trans e1, by linarith, ?_⟩
    nlinarith [abs_nonneg z.im]
  have hGup : ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖G z‖ ≤ ‖z - c‖ ^ (-(p + q * z.re)) * Real.exp Λ := by
    intro z h1 h2
    rw [hG, norm_weight p q c (hne z h1 h2)]
    gcongr
    exact hosc z h1 h2
  have hGlow : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → 0 ≤ z.im →
      ‖z - c‖ ^ (-(p + q * z.re)) ≤ ‖G z‖ := by
    intro z h1 h2 h3
    rw [hG, norm_weight p q c (hne z h1 h2)]
    have : 1 ≤ Real.exp (q * z.im * arg (-I * (z - c))) := Real.one_le_exp (hosc0 z h1 h2 h3)
    have hpos : 0 ≤ ‖z - c‖ ^ (-(p + q * z.re)) := Real.rpow_nonneg (norm_nonneg _) _
    nlinarith
  -- bounds on the boundary lines
  have hline : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ∀ e : ℝ, p + q * z.re = e →
      ‖f z‖ ≤ |M| * (1 + |z.im|) ^ e →
      ‖H z‖ ≤ |M| * ((1 / 2) ^ (-e) + D ^ (-e)) * Real.exp Λ := by
    intro z h1 h2 e he hfz
    have hGz := hGup z h1 h2
    rw [he] at hGz
    obtain ⟨_, d2, d3⟩ := hdist z h1 h2
    have hy0 : (0:ℝ) < 1 + |z.im| := by positivity
    have hr := rpow_le_of_le_of_le (e := -e) hy0 d2 d3
    have hy : (1 + |z.im|) ^ e * (1 + |z.im|) ^ (-e) = 1 := by
      rw [Real.rpow_neg hy0.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hy0 _).ne']
    calc ‖H z‖ = ‖f z‖ * ‖G z‖ := norm_mul _ _
      _ ≤ (|M| * (1 + |z.im|) ^ e) * (‖z - c‖ ^ (-e) * Real.exp Λ) :=
          mul_le_mul hfz hGz (norm_nonneg _) (by positivity)
      _ ≤ (|M| * (1 + |z.im|) ^ e) *
            ((((1 / 2) ^ (-e) + D ^ (-e)) * (1 + |z.im|) ^ (-e)) * Real.exp Λ) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right hr (Real.exp_pos _).le
      _ = |M| * ((1 / 2) ^ (-e) + D ^ (-e)) * Real.exp Λ *
            ((1 + |z.im|) ^ e * (1 + |z.im|) ^ (-e)) := by ring
      _ = |M| * ((1 / 2) ^ (-e) + D ^ (-e)) * Real.exp Λ := by rw [hy, mul_one]
  have hHa : ∀ z : ℂ, z.re = a → ‖H z‖ ≤ |M| * ((1 / 2) ^ (-α) + D ^ (-α)) * Real.exp Λ := by
    intro z hz
    refine hline z hz.ge (by linarith) α (by rw [hz, hpa]) ?_
    have := ha z.im
    rw [← hz, re_add_im] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self _)
      (Real.rpow_nonneg (by positivity) _))
  have hHb : ∀ z : ℂ, z.re = b → ‖H z‖ ≤ |M| * ((1 / 2) ^ (-β) + D ^ (-β)) * Real.exp Λ := by
    intro z hz
    refine hline z (by linarith) hz.le β (by rw [hz, hpb]) ?_
    have := hb z.im
    rw [← hz, re_add_im] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self _)
      (Real.rpow_nonneg (by positivity) _))
  -- a priori bound
  set E0 : ℝ := |α| + |β| with hE0
  have hexp : ∀ x, a ≤ x → x ≤ b → -(p + q * x) ≤ E0 := by
    intro x h1 h2
    have key : (b - a) * (p + q * x) = (b - x) * α + (x - a) * β := by
      rw [← hpa, ← hpb]; ring
    have k1 : -((b - x) * α) ≤ (b - x) * |α| := by
      rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (neg_le_abs α) (by linarith)
    have k2 : -((x - a) * β) ≤ (x - a) * |β| := by
      rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (neg_le_abs β) (by linarith)
    have k3 : (b - x) * |α| ≤ (b - a) * |α| :=
      mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    have k4 : (x - a) * |β| ≤ (b - a) * |β| :=
      mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    have : (b - a) * (-(p + q * x)) ≤ (b - a) * E0 := by
      rw [mul_neg, key, hE0]; linarith
    exact le_of_mul_le_mul_left this hba
  have hE0nn : 0 ≤ E0 := by positivity
  have hpoly' : ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖H z‖ ≤ |K| * D ^ E0 * Real.exp Λ * (1 + |z.im|) ^ (N + E0) := by
    intro z h1 h2
    obtain ⟨d1, _, d3⟩ := hdist z h1 h2
    have hy0 : (0:ℝ) < 1 + |z.im| := by positivity
    have hfz : ‖f z‖ ≤ |K| * (1 + |z.im|) ^ N :=
      (hpoly z h1 h2).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    have hG1 := hGup z h1 h2
    have hG2 : ‖z - c‖ ^ (-(p + q * z.re)) ≤ ‖z - c‖ ^ E0 :=
      Real.rpow_le_rpow_of_exponent_le d1 (hexp _ h1 h2)
    have hG3 : ‖z - c‖ ^ E0 ≤ (D * (1 + |z.im|)) ^ E0 :=
      Real.rpow_le_rpow (norm_nonneg _) d3 hE0nn
    rw [Real.mul_rpow (by linarith) hy0.le] at hG3
    calc ‖H z‖ = ‖f z‖ * ‖G z‖ := norm_mul _ _
      _ ≤ (|K| * (1 + |z.im|) ^ N) * (D ^ E0 * (1 + |z.im|) ^ E0 * Real.exp Λ) := by
          refine mul_le_mul hfz ?_ (norm_nonneg _) (by positivity)
          calc ‖G z‖ ≤ ‖z - c‖ ^ (-(p + q * z.re)) * Real.exp Λ := hG1
            _ ≤ D ^ E0 * (1 + |z.im|) ^ E0 * Real.exp Λ :=
                mul_le_mul_of_nonneg_right (hG2.trans hG3) (Real.exp_pos _).le
      _ = |K| * D ^ E0 * Real.exp Λ * ((1 + |z.im|) ^ N * (1 + |z.im|) ^ E0) := by ring
      _ = |K| * D ^ E0 * Real.exp Λ * (1 + |z.im|) ^ (N + E0) := by
          rw [← Real.rpow_add hy0]
  set K' : ℝ := |K| * D ^ E0 * Real.exp Λ with hK'
  set N' : ℝ := N + E0 with hN'
  have hN'nn : 0 ≤ N' := by positivity
  set c' : ℝ := Real.pi / (2 * (b - a)) with hc'
  have hc'pos : 0 < c' := by positivity
  have hc'lt : c' < Real.pi / (b - a) := by
    rw [hc']; exact div_lt_div_of_pos_left Real.pi_pos hba (by linarith)
  set B : ℝ := N' / c' with hB
  have hgrowth : ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖H z‖ ≤ K' * Real.exp (B * Real.exp (c' * |z.im|)) := by
    intro z h1 h2
    refine (hpoly' z h1 h2).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have e1 : (1 + |z.im|) ^ N' ≤ (Real.exp |z.im|) ^ N' :=
      Real.rpow_le_rpow (by positivity) (by linarith [Real.add_one_le_exp |z.im|]) hN'nn
    have e2 : (Real.exp |z.im|) ^ N' = Real.exp (N' * |z.im|) := by
      rw [← Real.exp_mul, mul_comm]
    have e3 : N' * |z.im| ≤ B * Real.exp (c' * |z.im|) := by
      have : c' * |z.im| ≤ Real.exp (c' * |z.im|) := by
        linarith [Real.add_one_le_exp (c' * |z.im|)]
      calc N' * |z.im| = B * (c' * |z.im|) := by rw [hB]; field_simp
        _ ≤ B * Real.exp (c' * |z.im|) := mul_le_mul_of_nonneg_left this (by positivity)
    calc (1 + |z.im|) ^ N' ≤ (Real.exp |z.im|) ^ N' := e1
      _ = Real.exp (N' * |z.im|) := e2
      _ ≤ Real.exp (B * Real.exp (c' * |z.im|)) := Real.exp_le_exp.mpr e3
  have hO : H =O[comap (_root_.abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)]
      fun z => Real.exp (B * Real.exp (c' * |z.im|)) := by
    refine IsBigO.of_bound K' (eventually_inf_principal.mpr (Eventually.of_forall fun z hz => ?_))
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hgrowth z hz.1.le hz.2.le
  have hGd : DiffContOnCl ℂ G (re ⁻¹' Ioo a b) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_preimage_re, closure_Ioo hab.ne]
    intro z hz
    exact (differentiableAt_weight p q c (hne z hz.1 hz.2)).differentiableWithinAt
  have hHd : DiffContOnCl ℂ H (re ⁻¹' Ioo a b) := ⟨hf.1.mul hGd.1, hf.2.mul hGd.2⟩
  set C0 : ℝ := max (|M| * ((1 / 2) ^ (-α) + D ^ (-α)) * Real.exp Λ)
    (|M| * ((1 / 2) ^ (-β) + D ^ (-β)) * Real.exp Λ) with hC0
  have hPL : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖H z‖ ≤ C0 := fun z h1 h2 =>
    PhragmenLindelof.vertical_strip hHd ⟨c', hc'lt, B, hO⟩
      (fun z hz => (hHa z hz).trans (le_max_left _ _))
      (fun z hz => (hHb z hz).trans (le_max_right _ _)) h1 h2
  -- conclusion
  set e : ℝ := p + q * σ with he
  refine ⟨C0 * ((1 / 2) ^ e + D ^ e), fun t ht => ?_⟩
  have hzre : ((σ : ℂ) + t * I).re = σ := by simp
  have hzim : ((σ : ℂ) + t * I).im = t := by simp
  have h1 : a ≤ ((σ : ℂ) + t * I).re := by rw [hzre]; exact hσa
  have h2 : ((σ : ℂ) + t * I).re ≤ b := by rw [hzre]; exact hσb
  obtain ⟨d1, d2, d3⟩ := hdist _ h1 h2
  have hlow := hGlow _ h1 h2 (by rw [hzim]; exact ht)
  rw [hzre] at hlow
  have hH1 := hPL _ h1 h2
  have hmain : ‖f (σ + t * I)‖ * ‖(σ + t * I : ℂ) - c‖ ^ (-e) ≤ C0 :=
    (mul_le_mul_of_nonneg_left hlow (norm_nonneg _)).trans (by rw [← norm_mul]; exact hH1)
  have hpos : 0 < ‖(σ + t * I : ℂ) - c‖ := by linarith
  have hfz : ‖f (σ + t * I)‖ ≤ C0 * ‖(σ + t * I : ℂ) - c‖ ^ e := by
    rw [Real.rpow_neg hpos.le] at hmain
    have hp : 0 < ‖(σ + t * I : ℂ) - c‖ ^ e := Real.rpow_pos_of_pos hpos _
    rwa [← div_eq_mul_inv, div_le_iff₀ hp] at hmain
  have hr := rpow_le_of_le_of_le (e := e) (by positivity : (0:ℝ) < 1 + |((σ : ℂ) + t * I).im|)
    d2 d3
  rw [hzim, abs_of_nonneg ht] at hr
  have hC0nn : 0 ≤ C0 := (norm_nonneg _).trans hH1
  calc ‖f (σ + t * I)‖ ≤ C0 * ‖(σ + t * I : ℂ) - c‖ ^ e := hfz
    _ ≤ C0 * (((1 / 2) ^ e + D ^ e) * (1 + t) ^ e) := mul_le_mul_of_nonneg_left hr hC0nn
    _ = C0 * ((1 / 2) ^ e + D ^ e) * (1 + t) ^ e := by ring

/-- **Phragmén–Lindelöf with different exponents** (one-sided in `t`).
Let `f` be holomorphic on the open strip `a < Re s < b`, continuous on its closure, with a
polynomial a-priori bound on the closed strip.  If `‖f(a+it)‖ ≤ M(1+|t|)^α` and
`‖f(b+it)‖ ≤ M(1+|t|)^β` for all real `t`, then for every `σ ∈ [a, b]` there is `C` with
`‖f(σ+it)‖ ≤ C (1+t)^{((b-σ)α + (σ-a)β)/(b-a)}` for all `t ≥ 0`. -/
theorem pl_interp {a b : ℝ} (hab : a < b) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (re ⁻¹' Ioo a b))
    {K N : ℝ} (hN : 0 ≤ N)
    (hpoly : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖f z‖ ≤ K * (1 + |z.im|) ^ N)
    {M α β : ℝ} (ha : ∀ t : ℝ, ‖f (a + t * I)‖ ≤ M * (1 + |t|) ^ α)
    (hb : ∀ t : ℝ, ‖f (b + t * I)‖ ≤ M * (1 + |t|) ^ β)
    {σ : ℝ} (hσa : a ≤ σ) (hσb : σ ≤ b) :
    ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
      ‖f (σ + t * I)‖ ≤ C * (1 + t) ^ (((b - σ) * α + (σ - a) * β) / (b - a)) := by
  have hba : 0 < b - a := sub_pos.mpr hab
  set q : ℝ := (β - α) / (b - a) with hq
  set p : ℝ := α - q * a with hp
  have hpa : p + q * a = α := by rw [hp]; ring
  have hpb : p + q * b = β := by rw [hp, hq]; field_simp; ring
  have he : p + q * σ = ((b - σ) * α + (σ - a) * β) / (b - a) := by
    rw [hp, hq]; field_simp; ring
  rw [← he]
  by_cases hq0 : 0 ≤ q
  · refine pl_core hab hf hN hpoly ha hb hpa hpb (c := b + 1) (fun x h1 h2 => ?_)
      (fun x h1 h2 => ?_) (fun x h1 h2 => mul_nonneg hq0 (by linarith)) hσa hσb
    · rw [abs_of_pos (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  · push Not at hq0
    refine pl_core hab hf hN hpoly ha hb hpa hpb (c := a - 1) (fun x h1 h2 => ?_)
      (fun x h1 h2 => ?_) (fun x h1 h2 => mul_nonneg_of_nonpos_of_nonpos hq0.le (by linarith))
      hσa hσb
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_neg (by linarith)]; linarith


/-- Polynomial a-priori bound for `ζ₁ = (s-1)ζ(s)` on any strip `σ₀ ≤ Re s ≤ σ₁` with `σ₀ > 0`
(ready to feed into `pl_interp` with `N = 2`). -/
theorem norm_riemannZeta₁_le_poly {σ₀ σ₁ : ℝ} (h0 : 0 < σ₀) (z : ℂ) (h1 : σ₀ ≤ z.re)
    (h2 : z.re ≤ σ₁) :
    ‖riemannZeta₁ z‖ ≤ ((|σ₁| + 1) + (|σ₁| + 1) ^ 2 / σ₀) * (1 + |z.im|) ^ (2 : ℝ) := by
  have hpos : 0 < z.re := lt_of_lt_of_le h0 h1
  have h := norm_riemannZeta₁_le hpos
  set S : ℝ := |σ₁| + 1 with hS
  have hS1 : 1 ≤ S := by rw [hS]; linarith [abs_nonneg σ₁]
  have hre : z.re ≤ |σ₁| := h2.trans (le_abs_self _)
  have ht : 0 ≤ |z.im| := abs_nonneg _
  have hz : ‖z‖ ≤ S * (1 + |z.im|) := by
    refine (norm_le_abs_re_add_abs_im z).trans ?_
    rw [abs_of_pos hpos]; nlinarith
  have hz1 : ‖z - 1‖ ≤ S * (1 + |z.im|) := by
    refine (norm_le_abs_re_add_abs_im _).trans ?_
    have : |(z - 1).re| ≤ S := by
      rw [abs_le]; simp; constructor <;> linarith
    have him : (z - 1).im = z.im := by simp
    rw [him]; nlinarith
  have hinv : 1 / z.re ≤ 1 / σ₀ := one_div_le_one_div_of_le h0 h1
  rw [Real.rpow_two]
  have hy : 1 ≤ 1 + |z.im| := by linarith
  calc ‖riemannZeta₁ z‖ ≤ ‖z‖ + ‖z‖ * ‖z - 1‖ / z.re := h
    _ = ‖z‖ + ‖z‖ * ‖z - 1‖ * (1 / z.re) := by ring
    _ ≤ S * (1 + |z.im|) + S * (1 + |z.im|) * (S * (1 + |z.im|)) * (1 / σ₀) := by
        gcongr
    _ = S * (1 + |z.im|) + S ^ 2 / σ₀ * (1 + |z.im|) ^ 2 := by ring
    _ ≤ S * (1 + |z.im|) ^ 2 + S ^ 2 / σ₀ * (1 + |z.im|) ^ 2 := by
        gcongr; nlinarith
    _ = (S + S ^ 2 / σ₀) * (1 + |z.im|) ^ 2 := by ring

/-! ## Symmetry and global bounds on vertical lines -/

lemma riemannZeta₁_conj (s : ℂ) : riemannZeta₁ ((starRingEnd ℂ) s) =
    (starRingEnd ℂ) (riemannZeta₁ s) := by
  rcases eq_or_ne s 1 with rfl | hs
  · simp
  · have hs' : (starRingEnd ℂ) s ≠ 1 := by
      intro h; apply hs
      have := congrArg (starRingEnd ℂ) h
      simpa using this
    rw [riemannZeta₁_eq_mul hs', riemannZeta₁_eq_mul hs, riemannZeta_conj, map_mul, map_sub,
      map_one]

lemma conj_line (σ t : ℝ) : ((σ : ℂ) + ((-t : ℝ) : ℂ) * I) = (starRingEnd ℂ) ((σ : ℂ) + t * I) := by
  apply Complex.ext <;> simp

lemma norm_riemannZeta_neg_im (σ t : ℝ) :
    ‖riemannZeta (σ + ((-t : ℝ) : ℂ) * I)‖ = ‖riemannZeta (σ + t * I)‖ := by
  rw [conj_line, riemannZeta_conj, Complex.norm_conj]

lemma norm_riemannZeta₁_neg_im (σ t : ℝ) :
    ‖riemannZeta₁ (σ + ((-t : ℝ) : ℂ) * I)‖ = ‖riemannZeta₁ (σ + t * I)‖ := by
  rw [conj_line, riemannZeta₁_conj, Complex.norm_conj]

/-- From a big-O bound at `+∞`, continuity, and the symmetry `‖g(-t)‖ = ‖g t‖`, get a bound
`‖g t‖ ≤ M (1+|t|)^e` valid for every real `t`. -/
lemma exists_global_bound {g : ℝ → ℂ} {e : ℝ} (hcont : Continuous g)
    (hsym : ∀ t, ‖g (-t)‖ = ‖g t‖) (hO : g =O[atTop] fun t : ℝ => t ^ e) :
    ∃ M : ℝ, ∀ t : ℝ, ‖g t‖ ≤ M * (1 + |t|) ^ e := by
  obtain ⟨C, hC⟩ := hO.bound
  obtain ⟨T0, hT0⟩ := eventually_atTop.mp hC
  set T1 := max T0 1 with hT1
  have hT11 : 1 ≤ T1 := le_max_right _ _
  have hbig : ∀ t, T1 ≤ t → ‖g t‖ ≤ |C| * ((1 / 2) ^ e + 1) * (1 + t) ^ e := by
    intro t ht
    have ht0 : T0 ≤ t := le_trans (le_max_left _ _) ht
    have ht1 : 1 ≤ t := le_trans hT11 ht
    have h := hT0 t ht0
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at h
    have hr := rpow_le_of_le_of_le (e := e) (x := t) (y := 1 + t) (D := 1) (by linarith)
      (by linarith) (by linarith)
    rw [Real.one_rpow] at hr
    calc ‖g t‖ ≤ C * t ^ e := h
      _ ≤ |C| * t ^ e :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (by linarith) _)
      _ ≤ |C| * (((1 / 2) ^ e + 1) * (1 + t) ^ e) :=
          mul_le_mul_of_nonneg_left hr (abs_nonneg _)
      _ = |C| * ((1 / 2) ^ e + 1) * (1 + t) ^ e := by ring
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := -T1) (b := T1)).exists_bound_of_continuousOn
    hcont.continuousOn
  set m := min 1 ((1 + T1) ^ e) with hm
  have hm0 : 0 < m := lt_min one_pos (Real.rpow_pos_of_pos (by positivity) _)
  have hsmall : ∀ t, |t| ≤ T1 → ‖g t‖ ≤ (|B| / m) * (1 + |t|) ^ e := by
    intro t ht
    have h1 : ‖g t‖ ≤ B := hB t (by
      rw [mem_Icc]; constructor <;> linarith [neg_abs_le t, le_abs_self t])
    have h2 : m ≤ (1 + |t|) ^ e := by
      rcases le_or_gt 0 e with he | he
      · exact (min_le_left _ _).trans (Real.one_le_rpow (by linarith [abs_nonneg t]) he)
      · exact (min_le_right _ _).trans
          (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) he.le)
    calc ‖g t‖ ≤ |B| := h1.trans (le_abs_self _)
      _ = (|B| / m) * m := by field_simp
      _ ≤ (|B| / m) * (1 + |t|) ^ e := mul_le_mul_of_nonneg_left h2 (by positivity)
  refine ⟨max (|C| * ((1 / 2) ^ e + 1)) (|B| / m), fun t => ?_⟩
  rcases le_or_gt |t| T1 with ht | ht
  · exact (hsmall t ht).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  · have h := hbig |t| ht.le
    have hgt : ‖g t‖ = ‖g |t|‖ := by
      rcases le_or_gt 0 t with h0 | h0
      · rw [abs_of_nonneg h0]
      · rw [abs_of_neg h0, hsym]
    rw [hgt]
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))

/-! ## `μ(1/2) ≥ 0` -/

lemma half_ne_one (t : ℝ) : (((1 / 2 : ℝ) : ℂ) + t * I) ≠ 1 := by
  intro h; have := congrArg re h; norm_num at this

/-- If `ζ(1/2+iT) = O(T^a)` as `T → +∞` then `ζ₁(1/2+iT) = O(T^{1+a})`. -/
lemma isBigO_riemannZeta₁_half {a : ℝ}
    (hO : (fun T : ℝ => riemannZeta (((1 / 2 : ℝ) : ℂ) + T * I)) =O[atTop] fun T : ℝ => T ^ a) :
    (fun T : ℝ => riemannZeta₁ (((1 / 2 : ℝ) : ℂ) + T * I)) =O[atTop]
      fun T : ℝ => T ^ (1 + a) := by
  have hlin : (fun T : ℝ => (((1 / 2 : ℝ) : ℂ) + T * I) - 1) =O[atTop]
      fun T : ℝ => T ^ (1 : ℝ) := by
    refine IsBigO.of_bound 2 ?_
    filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    rw [Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    have hre : ((((1 / 2 : ℝ) : ℂ) + t * I) - 1).re = -1 / 2 := by simp; norm_num
    have him : ((((1 / 2 : ℝ) : ℂ) + t * I) - 1).im = t := by simp
    have := norm_le_abs_re_add_abs_im ((((1 / 2 : ℝ) : ℂ) + t * I) - 1)
    rw [hre, him, abs_of_nonneg (by linarith : (0:ℝ) ≤ t)] at this
    have h12 : |(-1 / 2 : ℝ)| = 1 / 2 := by norm_num
    rw [h12] at this
    linarith
  have hprod := hlin.mul hO
  have hfun : ∀ T : ℝ, (((((1 / 2 : ℝ) : ℂ) + T * I) - 1) * riemannZeta (((1 / 2 : ℝ) : ℂ) + T * I))
      = riemannZeta₁ (((1 / 2 : ℝ) : ℂ) + T * I) := fun T =>
    (riemannZeta₁_eq_mul (half_ne_one T)).symm
  refine (hprod.congr_left hfun).trans_eventuallyEq ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
  rw [← Real.rpow_add hT]

/-- `ζ₁` is polynomially bounded on the strip `1/2 ≤ Re s ≤ 2`. -/
lemma norm_riemannZeta₁_le_strip (z : ℂ) (h1 : 1 / 2 ≤ z.re) (h2 : z.re ≤ 2) :
    ‖riemannZeta₁ z‖ ≤ 6 * (1 + |z.im|) ^ (2 : ℝ) := by
  have hpos : 0 < z.re := by linarith
  have h := norm_riemannZeta₁_le hpos
  have hz : ‖z‖ ≤ 2 * (1 + |z.im|) := by
    refine (norm_le_abs_re_add_abs_im z).trans ?_
    rw [abs_of_pos hpos]; linarith [abs_nonneg z.im]
  have hz1 : ‖z - 1‖ ≤ 1 + |z.im| := by
    refine (norm_le_abs_re_add_abs_im _).trans ?_
    have : |(z - 1).re| ≤ 1 := by
      rw [abs_le]; simp; constructor <;> linarith
    have him : (z - 1).im = z.im := by simp
    rw [him]; linarith
  have hinv : 1 / z.re ≤ 2 := by rw [div_le_iff₀ hpos]; linarith
  rw [Real.rpow_two]
  have ht : 0 ≤ |z.im| := abs_nonneg _
  calc ‖riemannZeta₁ z‖ ≤ ‖z‖ + ‖z‖ * ‖z - 1‖ / z.re := h
    _ = ‖z‖ + ‖z‖ * ‖z - 1‖ * (1 / z.re) := by ring
    _ ≤ 2 * (1 + |z.im|) + 2 * (1 + |z.im|) * (1 + |z.im|) * 2 := by
        gcongr
    _ ≤ 6 * (1 + |z.im|) ^ 2 := by nlinarith

/-- `0 ≤ μ(1/2)` (unconditionally), via Phragmén–Lindelöf on `1/2 ≤ Re s ≤ 2`. -/
theorem zero_le_mu_half : 0 ≤ mu (1 / 2) := by
  by_contra hneg
  push Not at hneg
  obtain ⟨a, ha1, ha2⟩ := EReal.lt_iff_exists_real_btwn.mp hneg
  have ha0 : a < 0 := by exact_mod_cast ha2
  have hO := isBigO_of_mu_lt ha1
  -- global bound on `Re s = 1/2`
  have hO1 := isBigO_riemannZeta₁_half hO
  obtain ⟨M1, hM1⟩ := exists_global_bound
    (g := fun t : ℝ => riemannZeta₁ (((1 / 2 : ℝ) : ℂ) + t * I))
    (differentiable_riemannZeta₁.continuous.comp (by fun_prop))
    (fun t => norm_riemannZeta₁_neg_im (1 / 2) t) hO1
  -- bound on `Re s = 2`
  obtain ⟨B2, hB2⟩ := exists_norm_riemannZeta_le (σ := 2) (by norm_num)
  have hM2 : ∀ t : ℝ, ‖riemannZeta₁ ((2 : ℝ) + t * I)‖ ≤ |B2| * (1 + |t|) ^ (1 : ℝ) := by
    intro t
    have hs1 : ((2 : ℝ) + t * I : ℂ) ≠ 1 := by
      intro h; have := congrArg re h; norm_num at this
    rw [riemannZeta₁_eq_mul hs1, norm_mul, Real.rpow_one]
    have h1 : ‖((2 : ℝ) + t * I : ℂ) - 1‖ ≤ 1 + |t| := by
      refine (norm_le_abs_re_add_abs_im _).trans ?_
      have hre : (((2 : ℝ) : ℂ) + t * I - 1).re = 1 := by simp; norm_num
      have him : (((2 : ℝ) : ℂ) + t * I - 1).im = t := by simp
      rw [hre, him]; norm_num
    have h2 : ‖riemannZeta ((2 : ℝ) + t * I)‖ ≤ |B2| :=
      (hB2 _ (by simp)).trans (le_abs_self _)
    calc ‖((2 : ℝ) + t * I : ℂ) - 1‖ * ‖riemannZeta ((2 : ℝ) + t * I)‖ ≤ (1 + |t|) * |B2| :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = |B2| * (1 + |t|) := by ring
  set M := max |M1| |B2| with hM
  have ha' : ∀ t : ℝ, ‖riemannZeta₁ (((1 / 2 : ℝ) : ℂ) + t * I)‖ ≤ M * (1 + |t|) ^ (1 + a) := by
    intro t
    refine (hM1 t).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact (le_abs_self _).trans (le_max_left _ _)
  have hb' : ∀ t : ℝ, ‖riemannZeta₁ ((2 : ℝ) + t * I)‖ ≤ M * (1 + |t|) ^ (1 : ℝ) := by
    intro t
    exact (hM2 t).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  -- Phragmén–Lindelöf at `σ = 3/2`
  obtain ⟨C, hC⟩ := pl_interp (a := 1 / 2) (b := 2) (by norm_num) (f := riemannZeta₁)
    differentiable_riemannZeta₁.diffContOnCl (K := 6) (N := 2) (by norm_num)
    norm_riemannZeta₁_le_strip ha' hb' (σ := 3 / 2) (by norm_num) (by norm_num)
  have hexp : (((2 : ℝ) - 3 / 2) * (1 + a) + (3 / 2 - 1 / 2) * 1) / (2 - 1 / 2) = 1 + a / 3 := by
    ring
  rw [hexp] at hC
  have hdecay : (fun T : ℝ => riemannZeta (((3 / 2 : ℝ) : ℂ) + T * I)) =O[atTop]
      fun T : ℝ => T ^ (a / 3) := by
    refine IsBigO.of_bound (4 * |C|) ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    have hs1 : (((3 / 2 : ℝ) : ℂ) + t * I) ≠ 1 := by
      intro h; have := congrArg re h; norm_num at this
    have hn : (1 + t) / 4 ≤ ‖(((3 / 2 : ℝ) : ℂ) + t * I) - 1‖ := by
      have e1 := abs_re_le_norm ((((3 / 2 : ℝ) : ℂ) + t * I) - 1)
      have e2 := abs_im_le_norm ((((3 / 2 : ℝ) : ℂ) + t * I) - 1)
      have hre : ((((3 / 2 : ℝ) : ℂ) + t * I) - 1).re = 1 / 2 := by simp; norm_num
      have him : ((((3 / 2 : ℝ) : ℂ) + t * I) - 1).im = t := by simp
      rw [hre, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)] at e1
      rw [him, abs_of_pos ht] at e2
      linarith
    have hnpos : 0 < ‖(((3 / 2 : ℝ) : ℂ) + t * I) - 1‖ := by linarith
    have h := hC t ht.le
    rw [riemannZeta₁_eq_mul hs1, norm_mul] at h
    have h1t : (0:ℝ) < 1 + t := by linarith
    rw [Real.rpow_add h1t, Real.rpow_one] at h
    have hpow : (1 + t) ^ (a / 3) ≤ t ^ (a / 3) :=
      Real.rpow_le_rpow_of_nonpos ht (by linarith) (by linarith)
    have hp0 : 0 ≤ (1 + t) ^ (a / 3) := Real.rpow_nonneg h1t.le _
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht.le _)]
    have key : ‖(((3 / 2 : ℝ) : ℂ) + t * I) - 1‖ * ‖riemannZeta (((3 / 2 : ℝ) : ℂ) + t * I)‖ ≤
        ‖(((3 / 2 : ℝ) : ℂ) + t * I) - 1‖ * (4 * |C| * (1 + t) ^ (a / 3)) := by
      calc _ ≤ C * ((1 + t) * (1 + t) ^ (a / 3)) := h
        _ ≤ |C| * ((1 + t) * (1 + t) ^ (a / 3)) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ ≤ |C| * ((4 * ‖(((3 / 2 : ℝ) : ℂ) + t * I) - 1‖) * (1 + t) ^ (a / 3)) := by
            gcongr; linarith
        _ = _ := by ring
    have key2 := le_of_mul_le_mul_left key hnpos
    calc ‖riemannZeta (((3 / 2 : ℝ) : ℂ) + t * I)‖ ≤ 4 * |C| * (1 + t) ^ (a / 3) := key2
      _ ≤ 4 * |C| * t ^ (a / 3) := mul_le_mul_of_nonneg_left hpow (by positivity)
  obtain ⟨c, hc, hlow⟩ := exists_pos_le_norm_riemannZeta_line (σ := 3 / 2) (by norm_num)
  have := nonneg_of_isBigO_of_norm_ge hc (Eventually.of_forall hlow) hdecay
  linarith

/-! ## Target 3 -/

lemma half_cast : (((1 / 2 : ℝ) : ℂ)) = 1 / 2 := by push_cast; ring

theorem mu_half_le_zero_of_lindelof (h : RiemannVonMangoldt.LindelofHypothesis) :
    mu (1 / 2) ≤ 0 := by
  by_contra hpos
  push Not at hpos
  obtain ⟨ε, h1, h2⟩ := EReal.lt_iff_exists_real_btwn.mp hpos
  have hε : 0 < ε := by exact_mod_cast h1
  have hO : (fun T : ℝ => riemannZeta (((1 / 2 : ℝ) : ℂ) + T * I)) =O[atTop]
      fun T : ℝ => T ^ ε := by
    rw [half_cast]; exact h ε hε
  have := mu_le_of_isBigO hO
  exact absurd (lt_of_lt_of_le h2 this) (lt_irrefl _)

theorem lindelof_iff_mu_half_eq_zero :
    RiemannVonMangoldt.LindelofHypothesis ↔ mu (1 / 2) = 0 := by
  constructor
  · intro h
    exact le_antisymm (mu_half_le_zero_of_lindelof h) zero_le_mu_half
  · intro h ε hε
    have hlt : mu (1 / 2) < (ε : EReal) := by rw [h]; exact_mod_cast hε
    have := isBigO_of_mu_lt hlt
    rw [half_cast] at this
    exact this

end LindelofHypothesis.LHC

open LindelofHypothesis in
theorem solution : RiemannVonMangoldt.LindelofHypothesis ↔ mu (1 / 2) = 0 :=
  LHC.lindelof_iff_mu_half_eq_zero
