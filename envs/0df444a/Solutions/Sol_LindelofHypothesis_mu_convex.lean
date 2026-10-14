-- Prove2me | solution 1 for LindelofHypothesis.mu_convex
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-13T02:42:48.320986+00:00
-- url     : https://prove2.me/submissions/7b73fb9b-adb5-4c10-b1dc-a4cbda6425e7

import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts

set_option autoImplicit false
open Complex Filter Asymptotics
open scoped ENNReal

/-!
# `μ` is finite and convex on all of `ℝ`

Helper namespace `LindelofHypothesis.LHD`.  No PL platform import: the Phragmén–Lindelöf step uses
Mathlib's `PhragmenLindelof.vertical_strip`.

Outline.
* `H := riemannZeta₁` (Mathlib, entire, `H s = (s - 1) ζ(s)` for `s ≠ 1`).
* `E σ e := ∃ C, ∀ t, ‖H (σ + t I)‖ ≤ C (1 + t²)^(e/2)` (whole-line polynomial bound).
* A priori bound `H_apriori`: `‖H s‖ ≤ A exp(D |Im s|)` on strips, `|Im s| ≥ 1`
  (via `ζ = (Λ₀ - 1/s - 1/(1-s)) / (π^(-s/2) Γ(s/2))`, `Λ₀` bounded on strips as a Mellin transform,
  `1/Γ(z) = Γ(1-z) sin(πz)/π` and `‖Γ(w)‖ ≤ Γ(p) + Γ(q)`).
* `E_interp`: convexity of the exponents of `E` (PL applied to `H(s) · exp(-(α+βs) log(K-s²)/2)`).
* `E_left_line`: `E (1/2 - n) (n+1)` from the functional equation, `|Γ(1/2+it)|² cosh(πt) = π` and
  `Γ(s+1) = sΓ(s)`.
* Conversions `E_of_isBigO`, `isBigO_of_E`; then finiteness of `μ` and convexity of `muR := toReal ∘ μ`.
-/

namespace LindelofHypothesis.LHD

open MeasureTheory Set
open scoped Real ComplexConjugate

/-! ## Copied from target 1 (`LHA`) -/

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


/-! ## Gamma, trigonometric and Mellin bounds; a priori bound for ζ -/

lemma rpow_le_rpow_add_rpow {t x p q : ℝ} (ht : 0 < t) (hp : p ≤ x) (hq : x ≤ q) :
    t ^ x ≤ t ^ p + t ^ q := by
  rcases le_total 1 t with h1 | h1
  · have := Real.rpow_le_rpow_of_exponent_le h1 hq
    have := Real.rpow_nonneg ht.le p
    linarith
  · have := Real.rpow_le_rpow_of_exponent_ge ht h1 hp
    have := Real.rpow_nonneg ht.le q
    linarith

lemma norm_Gamma_le {w : ℂ} {p q : ℝ} (hp : 0 < p) (hpw : p ≤ w.re) (hwq : w.re ≤ q) :
    ‖Complex.Gamma w‖ ≤ Real.Gamma p + Real.Gamma q := by
  have hw : 0 < w.re := hp.trans_le hpw
  rw [Complex.Gamma_eq_integral hw, Real.Gamma_eq_integral hp,
    Real.Gamma_eq_integral (hp.trans_le (hpw.trans hwq)), ← integral_add
      (Real.GammaIntegral_convergent hp) (Real.GammaIntegral_convergent (hp.trans_le (hpw.trans hwq)))]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine setIntegral_mono_on ?_ ((Real.GammaIntegral_convergent hp).add
    (Real.GammaIntegral_convergent (hp.trans_le (hpw.trans hwq)))) measurableSet_Ioi ?_
  · exact (Complex.GammaIntegral_convergent hw).norm
  · intro x hx
    have hx' : (0:ℝ) < x := hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      Complex.norm_cpow_eq_rpow_re_of_pos hx', ← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    simp only [sub_re, one_re]
    exact rpow_le_rpow_add_rpow hx' (by linarith) (by linarith)

lemma norm_sin_le_exp (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin]
  have h1 : ‖Complex.exp (-z * I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr (by simp; exact le_abs_self _)
  have h2 : ‖Complex.exp (z * I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr (by simp; exact neg_le_abs _)
  calc ‖(Complex.exp (-z * I) - Complex.exp (z * I)) * I / 2‖
      = ‖Complex.exp (-z * I) - Complex.exp (z * I)‖ / 2 := by simp
    _ ≤ (‖Complex.exp (-z * I)‖ + ‖Complex.exp (z * I)‖) / 2 := by
        gcongr; exact norm_sub_le _ _
    _ ≤ Real.exp |z.im| := by linarith

lemma Gamma_inv_eq {z : ℂ} (hz : z.im ≠ 0) :
    (Complex.Gamma z)⁻¹ = Complex.Gamma (1 - z) * Complex.sin (π * z) / π := by
  have hs : Complex.sin (π * z) ≠ 0 := by
    rw [Ne, Complex.sin_eq_zero_iff]
    rintro ⟨k, hk⟩
    have : z = k := by
      have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      field_simp at hk
      linear_combination hk
    apply hz; rw [this]; simp
  have h := Complex.Gamma_mul_Gamma_one_sub z
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hG : Complex.Gamma z ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h
    exact (div_ne_zero hπ hs) h.symm
  field_simp
  rw [h]; field_simp

lemma norm_mellin_le {f : ℝ → ℂ} {p q : ℝ} (hp : MellinConvergent f p) (hq : MellinConvergent f q)
    {s : ℂ} (h1 : p ≤ s.re) (h2 : s.re ≤ q) :
    ‖mellin f s‖ ≤ (∫ t in Ioi (0:ℝ), ‖(t:ℂ) ^ ((p:ℂ) - 1) • f t‖) +
      ∫ t in Ioi (0:ℝ), ‖(t:ℂ) ^ ((q:ℂ) - 1) • f t‖ := by
  rw [mellin, ← integral_add hp.norm hq.norm]
  refine norm_integral_le_of_norm_le (hp.norm.add hq.norm) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  have ht' : (0:ℝ) < t := ht
  simp only [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht', sub_re, one_re, ofReal_re, ← add_mul]
  exact mul_le_mul_of_nonneg_right (rpow_le_rpow_add_rpow ht' (by linarith) (by linarith))
    (norm_nonneg _)

lemma exists_bound_completedRiemannZeta₀ (a b : ℝ) :
    ∃ M : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖completedRiemannZeta₀ s‖ ≤ M := by
  set P := HurwitzZeta.hurwitzEvenFEPair 0
  have hc : ∀ w : ℂ, MellinConvergent P.f_modif w := fun w =>
    (P.isStrongFEPair_toStrongFEPair.hasMellin w).1
  refine ⟨((∫ t in Ioi (0:ℝ), ‖(t:ℂ) ^ (((a/2 : ℝ) : ℂ) - 1) • P.f_modif t‖) +
      ∫ t in Ioi (0:ℝ), ‖(t:ℂ) ^ (((b/2 : ℝ) : ℂ) - 1) • P.f_modif t‖) / 2, fun s ha hb => ?_⟩
  have h : completedRiemannZeta₀ s = P.Λ₀ (s / 2) / 2 := rfl
  rw [h, norm_div, Complex.norm_two]
  gcongr
  exact norm_mellin_le (hc _) (hc _) (by simp; linarith) (by simp; linarith)

/-- Crude bound for `ζ` in `a ≤ Re s ≤ 3/2`, `|Im s| ≥ 1`. -/
lemma zeta_apriori_left (a : ℝ) :
    ∃ A : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ 3/2 → 1 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ A * Real.exp (π / 2 * |s.im|) := by
  obtain ⟨M, hM⟩ := exists_bound_completedRiemannZeta₀ a (3/2)
  refine ⟨(M + 2) * (π ^ ((3:ℝ)/4) * ((Real.Gamma (1/4) + Real.Gamma (1 - a/2)) / π)),
    fun s ha hb ht => ?_⟩
  have hs0 : s ≠ 0 := by rintro rfl; simp at ht; linarith
  have hsn : 1 ≤ ‖s‖ := ht.trans (Complex.abs_im_le_norm s)
  have hsn' : 1 ≤ ‖1 - s‖ := by
    refine ht.trans (le_of_eq_of_le ?_ (Complex.abs_im_le_norm (1 - s)))
    simp
  rw [riemannZeta_eq_completedRiemannZeta₀ hs0, div_eq_mul_inv, norm_mul, mul_inv, norm_mul,
    norm_inv, Gamma_inv_eq (by simp; intro h; rw [h] at ht; simp at ht; linarith)]
  have hnum : ‖completedRiemannZeta₀ s - 1 / s - 1 / (1 - s)‖ ≤ M + 2 := by
    have h1 : ‖1 / s‖ ≤ 1 := by rw [norm_div, norm_one]; exact div_le_one_of_le₀ hsn (norm_nonneg _)
    have h2 : ‖1 / (1 - s)‖ ≤ 1 := by
      rw [norm_div, norm_one]; exact div_le_one_of_le₀ hsn' (norm_nonneg _)
    calc _ ≤ ‖completedRiemannZeta₀ s - 1 / s‖ + ‖1 / (1 - s)‖ := norm_sub_le _ _
      _ ≤ ‖completedRiemannZeta₀ s‖ + ‖1 / s‖ + ‖1 / (1 - s)‖ := by
          gcongr; exact norm_sub_le _ _
      _ ≤ M + 1 + 1 := by gcongr; exact hM s ha hb
      _ = M + 2 := by ring
  have hpi : ‖((π:ℂ) ^ (-s / 2))‖⁻¹ ≤ π ^ ((3:ℝ)/4) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, ← Real.rpow_neg Real.pi_pos.le]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three])
    simp; linarith
  have hG : ‖Complex.Gamma (1 - s / 2) * Complex.sin (π * (s / 2)) / π‖ ≤
      (Real.Gamma (1/4) + Real.Gamma (1 - a/2)) / π * Real.exp (π / 2 * |s.im|) := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      div_mul_eq_mul_div]
    have hΓ : ‖Complex.Gamma (1 - s / 2)‖ ≤ Real.Gamma (1/4) + Real.Gamma (1 - a/2) :=
      norm_Gamma_le (by norm_num) (by simp; linarith) (by simp; linarith)
    have hsin : ‖Complex.sin (π * (s / 2))‖ ≤ Real.exp (π / 2 * |s.im|) := by
      refine (norm_sin_le_exp _).trans (le_of_eq ?_)
      congr 1
      simp [abs_mul, abs_of_pos Real.pi_pos]
      rw [abs_div, abs_two]; ring
    exact div_le_div_of_nonneg_right (mul_le_mul hΓ hsin (norm_nonneg _)
      ((norm_nonneg _).trans hΓ)) Real.pi_pos.le
  have hnn : 0 ≤ M + 2 := (norm_nonneg _).trans hnum
  calc ‖completedRiemannZeta₀ s - 1 / s - 1 / (1 - s)‖ *
        (‖((π:ℂ) ^ (-s / 2))‖⁻¹ * ‖Complex.Gamma (1 - s / 2) * Complex.sin (π * (s / 2)) / π‖)
      ≤ (M + 2) * (π ^ ((3:ℝ)/4) *
        ((Real.Gamma (1/4) + Real.Gamma (1 - a/2)) / π * Real.exp (π / 2 * |s.im|))) := by
        gcongr
    _ = _ := by ring

/-! ## `H = riemannZeta₁` -/

lemma H_eq {s : ℂ} (hs : s ≠ 1) : riemannZeta₁ s = (s - 1) * riemannZeta s := by
  rw [riemannZeta_eq_inv_sub_mul hs]
  have : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  field_simp

/-- Crude bound for `ζ` on `Re s ≥ a`, `|Im s| ≥ 1`. -/
lemma zeta_apriori (a : ℝ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ s : ℂ, a ≤ s.re → 1 ≤ |s.im| →
    ‖riemannZeta s‖ ≤ A * Real.exp (π / 2 * |s.im|) := by
  obtain ⟨A₁, hA₁⟩ := zeta_apriori_left a
  obtain ⟨C₀, hC₀⟩ := exists_norm_riemannZeta_le (σ := 3/2) (by norm_num)
  refine ⟨|A₁| + |C₀|, by positivity, fun s ha ht => ?_⟩
  have he : 1 ≤ Real.exp (π / 2 * |s.im|) := Real.one_le_exp (by positivity)
  rcases le_total s.re (3/2) with h | h
  · calc ‖riemannZeta s‖ ≤ A₁ * Real.exp (π / 2 * |s.im|) := hA₁ s ha h ht
      _ ≤ (|A₁| + |C₀|) * Real.exp (π / 2 * |s.im|) := by
          gcongr; linarith [le_abs_self A₁, abs_nonneg C₀]
  · calc ‖riemannZeta s‖ ≤ C₀ := hC₀ s h
      _ ≤ |C₀| := le_abs_self _
      _ ≤ (|A₁| + |C₀|) * 1 := by linarith [abs_nonneg A₁]
      _ ≤ (|A₁| + |C₀|) * Real.exp (π / 2 * |s.im|) := by gcongr

lemma H_apriori (a b : ℝ) : ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
    1 ≤ |s.im| → ‖riemannZeta₁ s‖ ≤ A * Real.exp (D * |s.im|) := by
  obtain ⟨A, hA, hAs⟩ := zeta_apriori a
  refine ⟨(|a| + |b| + 1) * A, π / 2 + 1, by positivity, by positivity, fun s ha hb ht => ?_⟩
  have hs1 : s ≠ 1 := by rintro rfl; simp at ht; linarith
  rw [H_eq hs1, norm_mul]
  have hs : ‖s - 1‖ ≤ (|a| + |b| + 1) * Real.exp |s.im| := by
    have h1 : ‖s - 1‖ ≤ |s.re - 1| + |s.im| := by
      have := Complex.norm_le_abs_re_add_abs_im (s - 1); simpa using this
    have h2 : |s.re - 1| ≤ |a| + |b| + 1 := by
      rw [abs_le]; constructor <;>
        linarith [neg_abs_le a, le_abs_self b, abs_nonneg a, abs_nonneg b]
    have h3 := Real.add_one_le_exp |s.im|
    have h4 : 0 ≤ |a| + |b| := by positivity
    nlinarith [abs_nonneg s.im]
  calc ‖s - 1‖ * ‖riemannZeta s‖ ≤ ((|a| + |b| + 1) * Real.exp |s.im|) *
        (A * Real.exp (π / 2 * |s.im|)) := by gcongr; exact hAs s ha ht
    _ = (|a| + |b| + 1) * A * Real.exp ((π / 2 + 1) * |s.im|) := by
        rw [show (π / 2 + 1) * |s.im| = |s.im| + π / 2 * |s.im| by ring, Real.exp_add]; ring

/-- The weight `exp(-(α + β s) log(K - s²) / 2)`. -/
noncomputable def W (K α β : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (-((α:ℂ) + β * s) * Complex.log ((K:ℂ) - s ^ 2) / 2)

lemma re_K_sub_sq (K : ℝ) (s : ℂ) : ((K:ℂ) - s ^ 2).re = K - s.re ^ 2 + s.im ^ 2 := by
  simp [sq]; ring

lemma im_K_sub_sq (K : ℝ) (s : ℂ) : ((K:ℂ) - s ^ 2).im = -(2 * s.re * s.im) := by
  simp [sq]; ring

lemma differentiableAt_W {K α β : ℝ} {s : ℂ} (h : s.re ^ 2 < K) :
    DifferentiableAt ℂ (W K α β) s := by
  have hslit : (K:ℂ) - s ^ 2 ∈ slitPlane :=
    Or.inl (by rw [re_K_sub_sq]; nlinarith [sq_nonneg s.im])
  have : DifferentiableAt ℂ (fun s : ℂ => Complex.log ((K:ℂ) - s ^ 2)) s :=
    ((differentiableAt_const _).sub (differentiableAt_pow 2)).clog hslit
  unfold W
  fun_prop

lemma norm_W (K α β : ℝ) (s : ℂ) :
    ‖W K α β s‖ = Real.exp (-(α + β * s.re) * Real.log ‖(K:ℂ) - s ^ 2‖ / 2 +
      β * s.im * arg ((K:ℂ) - s ^ 2) / 2) := by
  rw [W, Complex.norm_exp]; congr 1
  simp [Complex.log_re, Complex.log_im]; ring

lemma norm_K_sub_sq_ge {K : ℝ} {s : ℂ} (h : s.re ^ 2 + 1 ≤ K) :
    1 + s.im ^ 2 ≤ ‖(K:ℂ) - s ^ 2‖ :=
  le_trans (by rw [re_K_sub_sq]; linarith) (Complex.re_le_norm _)

lemma norm_K_sub_sq_le {K : ℝ} {s : ℂ} (h : s.re ^ 2 ≤ K) (hK : 1 ≤ K) :
    ‖(K:ℂ) - s ^ 2‖ ≤ 2 * K * (1 + s.im ^ 2) := by
  refine (norm_sub_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith), norm_pow,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  nlinarith [sq_nonneg s.im]

lemma abs_im_mul_arg_le {K : ℝ} {s : ℂ} (h : s.re ^ 2 < K) :
    |s.im * arg ((K:ℂ) - s ^ 2)| ≤ π * |s.re| := by
  set z : ℂ := (K:ℂ) - s ^ 2 with hz
  have hre : 0 < z.re := by rw [hz, re_K_sub_sq]; nlinarith [sq_nonneg s.im]
  have hzn : 0 < ‖z‖ := hre.trans_le (Complex.re_le_norm _)
  have harg : |arg z| ≤ π / 2 := Complex.abs_arg_le_pi_div_two_iff.mpr hre.le
  have hsin : 2 / π * |arg z| ≤ |Real.sin (arg z)| := by
    rcases le_total 0 (arg z) with h0 | h0
    · rw [abs_of_nonneg h0, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h0
        (by linarith [abs_le.mp harg, Real.pi_pos]))]
      exact Real.mul_le_sin h0 (by linarith [le_abs_self (arg z)])
    · rw [abs_of_nonpos h0, abs_of_nonpos (Real.sin_nonpos_of_nonpos_of_neg_pi_le h0
        (by linarith [abs_le.mp harg, Real.pi_pos]))]
      have := Real.mul_le_sin (x := -arg z) (by linarith) (by linarith [neg_abs_le (arg z), abs_le.mp harg])
      rw [Real.sin_neg] at this
      linarith
  rw [Complex.sin_arg, abs_div, abs_of_pos hzn, hz, im_K_sub_sq, abs_neg, abs_mul, abs_mul,
    abs_two] at hsin
  have ht2 : s.im ^ 2 ≤ ‖z‖ := by
    refine le_trans ?_ (Complex.re_le_norm _); rw [hz, re_K_sub_sq]; nlinarith
  rw [← hz] at hsin
  have hπ := Real.pi_pos
  have key : |arg z| ≤ π * |s.re| * |s.im| / ‖z‖ := by
    rw [le_div_iff₀ hzn]
    have := (le_div_iff₀ hzn).mp hsin
    field_simp at this ⊢
    nlinarith
  rw [abs_mul]
  calc |s.im| * |arg z| ≤ |s.im| * (π * |s.re| * |s.im| / ‖z‖) := by gcongr
    _ = π * |s.re| * (s.im ^ 2 / ‖z‖) := by rw [← sq_abs s.im]; ring
    _ ≤ π * |s.re| * 1 := by
        gcongr; exact div_le_one_of_le₀ ht2 hzn.le
    _ = π * |s.re| := mul_one _

lemma rpow_le_max_mul {x y c e : ℝ} (hy : 0 < y) (h1 : y ≤ x) (h2 : x ≤ c * y) :
    x ^ e ≤ max 1 (c ^ e) * y ^ e := by
  have hx : 0 < x := hy.trans_le h1
  have hc : 1 ≤ c := by
    by_contra hc; have hc := not_le.mp hc; nlinarith
  rcases le_total 0 e with he | he
  · calc x ^ e ≤ (c * y) ^ e := Real.rpow_le_rpow hx.le h2 he
      _ = c ^ e * y ^ e := Real.mul_rpow (by linarith) hy.le
      _ ≤ max 1 (c ^ e) * y ^ e := by gcongr; exact le_max_right _ _
  · calc x ^ e ≤ y ^ e := Real.rpow_le_rpow_of_nonpos hy h1 he
      _ = 1 * y ^ e := (one_mul _).symm
      _ ≤ max 1 (c ^ e) * y ^ e := by gcongr; exact le_max_left _ _

lemma W_bounds {K α β : ℝ} {s : ℂ} (h : s.re ^ 2 < K) (B : ℝ) (hB : |β| * π * |s.re| / 2 ≤ B) :
    ‖W K α β s‖ ≤ ‖(K:ℂ) - s ^ 2‖ ^ (-(α + β * s.re) / 2) * Real.exp B ∧
    ‖(K:ℂ) - s ^ 2‖ ^ (-(α + β * s.re) / 2) * Real.exp (-B) ≤ ‖W K α β s‖ := by
  have hre : 0 < ((K:ℂ) - s ^ 2).re := by rw [re_K_sub_sq]; nlinarith [sq_nonneg s.im]
  have hx : 0 < ‖(K:ℂ) - s ^ 2‖ := hre.trans_le (Complex.re_le_norm _)
  have habs := abs_im_mul_arg_le h
  have h2 : |β * s.im * arg ((K:ℂ) - s ^ 2) / 2| ≤ B := by
    rw [mul_assoc, abs_div, abs_mul, abs_two]
    have := mul_le_mul_of_nonneg_left habs (abs_nonneg β)
    linarith
  rw [norm_W, Real.rpow_def_of_pos hx, ← Real.exp_add, ← Real.exp_add]
  constructor <;> apply Real.exp_le_exp.mpr
  · have := (abs_le.mp h2).2; linarith
  · have := (abs_le.mp h2).1; linarith

/-- Whole-line polynomial bound for `H = riemannZeta₁ = (s-1) ζ(s)`. -/
def E (σ e : ℝ) : Prop :=
  ∃ C : ℝ, ∀ t : ℝ, ‖riemannZeta₁ (σ + t * I)‖ ≤ C * (1 + t ^ 2) ^ (e / 2)

lemma isBigO_exp_exp_of_bound {a b A D : ℝ} (hab : a < b) (hA : 0 ≤ A) (hD : 0 ≤ D) {f : ℂ → ℂ}
    (hf : ∀ z : ℂ, a < z.re → z.re < b → 1 ≤ |z.im| → ‖f z‖ ≤ A * Real.exp (D * |z.im|)) :
    ∃ c < π / (b - a), ∃ B, f =O[comap (_root_.abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)]
      fun z ↦ Real.exp (B * Real.exp (c * |z.im|)) := by
  have hc : 0 < π / (b - a) / 2 := by have := sub_pos.mpr hab; positivity
  refine ⟨π / (b - a) / 2, by linarith, A + D / (π / (b - a) / 2), ?_⟩
  set c := π / (b - a) / 2
  refine IsBigO.of_bound 1 ?_
  have hmem : (_root_.abs ∘ im) ⁻¹' Ici 1 ∩ re ⁻¹' Ioo a b ∈
      comap (_root_.abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b) :=
    inter_mem_inf (preimage_mem_comap (Ici_mem_atTop 1)) (mem_principal_self _)
  filter_upwards [hmem] with z ⟨hz1, hz2⟩
  have hz1' : 1 ≤ |z.im| := hz1
  rw [one_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hexp : 1 ≤ Real.exp (c * |z.im|) := Real.one_le_exp (by positivity)
  have hlin : c * |z.im| ≤ Real.exp (c * |z.im|) := by
    linarith [Real.add_one_le_exp (c * |z.im|)]
  calc ‖f z‖ ≤ A * Real.exp (D * |z.im|) := hf z hz2.1 hz2.2 hz1'
    _ ≤ Real.exp A * Real.exp (D * |z.im|) := by
        gcongr; linarith [Real.add_one_le_exp A]
    _ = Real.exp (A + D * |z.im|) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((A + D / c) * Real.exp (c * |z.im|)) := by
        apply Real.exp_le_exp.mpr
        have h1 : A ≤ A * Real.exp (c * |z.im|) := le_mul_of_one_le_right hA hexp
        have h2 : D * |z.im| ≤ D / c * Real.exp (c * |z.im|) := by
          calc D * |z.im| = D / c * (c * |z.im|) := by field_simp
            _ ≤ D / c * Real.exp (c * |z.im|) := by gcongr
        nlinarith

lemma one_add_sq_le_exp (t : ℝ) : 1 + t ^ 2 ≤ Real.exp (2 * |t|) := by
  have h := Real.add_one_le_exp |t|
  have h2 : Real.exp (2 * |t|) = Real.exp |t| ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h2]
  have : (|t| + 1) ^ 2 ≤ Real.exp |t| ^ 2 := pow_le_pow_left₀ (by positivity) h 2
  nlinarith [sq_abs t, abs_nonneg t]

/-- Phragmén–Lindelöf convexity for the whole-line bounds `E`. -/
theorem E_interp {σ₁ σ₂ e₁ e₂ : ℝ} (h12 : σ₁ < σ₂) (h1 : E σ₁ e₁) (h2 : E σ₂ e₂) {σ : ℝ}
    (hσ1 : σ₁ ≤ σ) (hσ2 : σ ≤ σ₂) : E σ (e₁ + (σ - σ₁) / (σ₂ - σ₁) * (e₂ - e₁)) := by
  obtain ⟨C₁, hC₁⟩ := h1
  obtain ⟨C₂, hC₂⟩ := h2
  have hd : 0 < σ₂ - σ₁ := sub_pos.mpr h12
  set β : ℝ := (e₂ - e₁) / (σ₂ - σ₁) with hβ
  set α : ℝ := e₁ - β * σ₁ with hα
  have he₁ : α + β * σ₁ = e₁ := by rw [hα]; ring
  have he₂ : α + β * σ₂ = e₂ := by rw [hα, hβ]; field_simp; ring
  have heσ : e₁ + (σ - σ₁) / (σ₂ - σ₁) * (e₂ - e₁) = α + β * σ := by
    rw [hα, hβ]; field_simp; ring
  rw [heσ]
  set m : ℝ := |σ₁| + |σ₂| with hm
  set K : ℝ := m ^ 2 + 1 with hK
  have hK1 : 1 ≤ K := by nlinarith [sq_nonneg m]
  have hxm : ∀ x : ℝ, σ₁ ≤ x → x ≤ σ₂ → |x| ≤ m := by
    intro x hx1 hx2
    rw [abs_le]; constructor
    · linarith [neg_abs_le σ₁, abs_nonneg σ₂]
    · linarith [le_abs_self σ₂, abs_nonneg σ₁]
  have hKx : ∀ x : ℝ, σ₁ ≤ x → x ≤ σ₂ → x ^ 2 + 1 ≤ K := by
    intro x hx1 hx2
    have := hxm x hx1 hx2
    have : x ^ 2 ≤ m ^ 2 := by
      rw [← sq_abs x]; exact pow_le_pow_left₀ (abs_nonneg x) this 2
    linarith
  set B₀ : ℝ := |β| * π * m / 2 with hB₀
  have hB₀x : ∀ x : ℝ, σ₁ ≤ x → x ≤ σ₂ → |β| * π * |x| / 2 ≤ B₀ := by
    intro x hx1 hx2
    have := hxm x hx1 hx2
    rw [hB₀]
    have : |β| * π * |x| ≤ |β| * π * m := by gcongr
    linarith
  set F : ℂ → ℂ := fun z => riemannZeta₁ z * W K α β z with hF
  -- boundary bounds
  have hbd : ∀ (σj ej Cj : ℝ), σ₁ ≤ σj → σj ≤ σ₂ → α + β * σj = ej →
      (∀ t : ℝ, ‖riemannZeta₁ (σj + t * I)‖ ≤ Cj * (1 + t ^ 2) ^ (ej / 2)) →
      ∀ z : ℂ, z.re = σj → ‖F z‖ ≤ Cj * max 1 ((2 * K) ^ (-ej / 2)) * Real.exp B₀ := by
    intro σj ej Cj hj1 hj2 hej hCj z hz
    have hz' : z = (σj : ℂ) + (z.im : ℂ) * I := by rw [← hz]; exact (Complex.re_add_im z).symm
    have hCj0 : 0 ≤ Cj := by
      have := hCj 0; simp at this; exact (norm_nonneg _).trans this
    have hzK : z.re ^ 2 + 1 ≤ K := hz ▸ hKx σj hj1 hj2
    have hWb := (W_bounds (K := K) (α := α) (β := β) (s := z) (by linarith) B₀ (hz ▸ hB₀x σj hj1 hj2)).1
    rw [hz, hej] at hWb
    have hy : 0 < 1 + z.im ^ 2 := by positivity
    have hr := rpow_le_max_mul (e := -ej / 2) hy (norm_K_sub_sq_ge hzK)
      (norm_K_sub_sq_le (by linarith) hK1)
    have hH := hCj z.im
    rw [← hz'] at hH
    have hcancel : (1 + z.im ^ 2) ^ (ej / 2) * (1 + z.im ^ 2) ^ (-ej / 2) = 1 := by
      rw [← Real.rpow_add hy, show ej / 2 + -ej / 2 = 0 by ring, Real.rpow_zero]
    calc ‖F z‖ = ‖riemannZeta₁ z‖ * ‖W K α β z‖ := norm_mul _ _
      _ ≤ (Cj * (1 + z.im ^ 2) ^ (ej / 2)) *
          (max 1 ((2 * K) ^ (-ej / 2)) * (1 + z.im ^ 2) ^ (-ej / 2) * Real.exp B₀) := by
          gcongr
          exact hWb.trans (by gcongr)
      _ = Cj * max 1 ((2 * K) ^ (-ej / 2)) * Real.exp B₀ *
          ((1 + z.im ^ 2) ^ (ej / 2) * (1 + z.im ^ 2) ^ (-ej / 2)) := by ring
      _ = Cj * max 1 ((2 * K) ^ (-ej / 2)) * Real.exp B₀ := by rw [hcancel, mul_one]
  set Cb : ℝ := max (C₁ * max 1 ((2 * K) ^ (-e₁ / 2)) * Real.exp B₀)
    (C₂ * max 1 ((2 * K) ^ (-e₂ / 2)) * Real.exp B₀) with hCb
  have hle_a : ∀ z : ℂ, z.re = σ₁ → ‖F z‖ ≤ Cb := fun z hz =>
    (hbd σ₁ e₁ C₁ le_rfl h12.le he₁ hC₁ z hz).trans (le_max_left _ _)
  have hle_b : ∀ z : ℂ, z.re = σ₂ → ‖F z‖ ≤ Cb := fun z hz =>
    (hbd σ₂ e₂ C₂ h12.le le_rfl he₂ hC₂ z hz).trans (le_max_right _ _)
  -- differentiability
  have hdiff : DiffContOnCl ℂ F (re ⁻¹' Ioo σ₁ σ₂) := by
    apply DifferentiableOn.diffContOnCl
    rw [Complex.closure_preimage_re, closure_Ioo h12.ne]
    intro z hz
    have hzK : z.re ^ 2 + 1 ≤ K := hKx z.re hz.1 hz.2
    exact ((differentiable_riemannZeta₁ z).mul
      (differentiableAt_W (by linarith))).differentiableWithinAt
  -- a priori bound
  obtain ⟨A, D, hA, hD, hAD⟩ := H_apriori σ₁ σ₂
  set P : ℝ := (|e₁| + |e₂|) / 2 with hP
  have hP0 : 0 ≤ P := by positivity
  have hexpo : ∀ x : ℝ, σ₁ ≤ x → x ≤ σ₂ → -(α + β * x) / 2 ≤ P := by
    intro x hx1 hx2
    set l := (x - σ₁) / (σ₂ - σ₁) with hl
    have hl0 : 0 ≤ l := div_nonneg (by linarith) hd.le
    have hl1 : l ≤ 1 := (div_le_one hd).mpr (by linarith)
    have hlin : α + β * x = (1 - l) * e₁ + l * e₂ := by
      rw [hl, hα, hβ]; field_simp; ring
    rw [hlin, hP]
    have h1' := mul_le_mul_of_nonneg_left (neg_le_abs e₁) (by linarith : (0:ℝ) ≤ 1 - l)
    have h2' := mul_le_mul_of_nonneg_left (neg_le_abs e₂) hl0
    nlinarith [abs_nonneg e₁, abs_nonneg e₂]
  have hB : ∃ c < π / (σ₂ - σ₁), ∃ B, F =O[comap (_root_.abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo σ₁ σ₂)]
      fun z ↦ Real.exp (B * Real.exp (c * |z.im|)) := by
    refine isBigO_exp_exp_of_bound (A := A * (2 * K) ^ P * Real.exp B₀) (D := D + 2 * P) h12
      (by positivity) (by positivity) ?_
    intro z hz1 hz2 hzi
    have hzK : z.re ^ 2 + 1 ≤ K := hKx z.re hz1.le hz2.le
    have hWb := (W_bounds (K := K) (α := α) (β := β) (s := z) (by linarith) B₀ (hB₀x z.re hz1.le hz2.le)).1
    have hx1 : 1 ≤ ‖(K:ℂ) - z ^ 2‖ := le_trans (by nlinarith [sq_nonneg z.im])
      (norm_K_sub_sq_ge hzK)
    have hxP : ‖(K:ℂ) - z ^ 2‖ ^ (-(α + β * z.re) / 2) ≤ (2 * K) ^ P * Real.exp (2 * |z.im| * P) := by
      calc ‖(K:ℂ) - z ^ 2‖ ^ (-(α + β * z.re) / 2) ≤ ‖(K:ℂ) - z ^ 2‖ ^ P :=
            Real.rpow_le_rpow_of_exponent_le hx1 (hexpo z.re hz1.le hz2.le)
        _ ≤ (2 * K * Real.exp (2 * |z.im|)) ^ P := by
            apply Real.rpow_le_rpow (norm_nonneg _) _ hP0
            exact (norm_K_sub_sq_le (by linarith) hK1).trans
              (by gcongr; exact one_add_sq_le_exp _)
        _ = (2 * K) ^ P * Real.exp (2 * |z.im| * P) := by
            rw [Real.mul_rpow (by positivity) (by positivity), ← Real.exp_mul]
    calc ‖F z‖ = ‖riemannZeta₁ z‖ * ‖W K α β z‖ := norm_mul _ _
      _ ≤ (A * Real.exp (D * |z.im|)) *
          ((2 * K) ^ P * Real.exp (2 * |z.im| * P) * Real.exp B₀) := by
          gcongr
          · exact hAD z hz1.le hz2.le hzi
          · exact hWb.trans (by gcongr)
      _ = A * (2 * K) ^ P * Real.exp B₀ * Real.exp ((D + 2 * P) * |z.im|) := by
          rw [show (D + 2 * P) * |z.im| = D * |z.im| + 2 * |z.im| * P by ring, Real.exp_add]
          ring
  -- conclude
  refine ⟨Cb * max 1 ((2 * K) ^ ((α + β * σ) / 2)) * Real.exp B₀, fun t => ?_⟩
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have hPL : ‖F s‖ ≤ Cb := PhragmenLindelof.vertical_strip hdiff hB hle_a hle_b
    (by rw [hsre]; exact hσ1) (by rw [hsre]; exact hσ2)
  have hsK : s.re ^ 2 + 1 ≤ K := hsre ▸ hKx σ hσ1 hσ2
  have hWb := (W_bounds (K := K) (α := α) (β := β) (s := s) (by linarith) B₀ (hsre ▸ hB₀x σ hσ1 hσ2)).2
  rw [hsre] at hWb
  have hxpos : 0 < ‖(K:ℂ) - s ^ 2‖ := by
    have := norm_K_sub_sq_ge hsK; nlinarith [sq_nonneg s.im]
  have hy : 0 < 1 + t ^ 2 := by positivity
  have hr := rpow_le_max_mul (e := (α + β * σ) / 2) hy (hsim ▸ norm_K_sub_sq_ge hsK)
    (hsim ▸ norm_K_sub_sq_le (by linarith) hK1)
  set x := ‖(K:ℂ) - s ^ 2‖ with hx
  have hcancel : x ^ (-(α + β * σ) / 2) * x ^ ((α + β * σ) / 2) = 1 := by
    rw [← Real.rpow_add hxpos, show -(α + β * σ) / 2 + (α + β * σ) / 2 = 0 by ring,
      Real.rpow_zero]
  have hFs : ‖riemannZeta₁ s‖ * (x ^ (-(α + β * σ) / 2) * Real.exp (-B₀)) ≤ Cb := by
    calc ‖riemannZeta₁ s‖ * (x ^ (-(α + β * σ) / 2) * Real.exp (-B₀))
        ≤ ‖riemannZeta₁ s‖ * ‖W K α β s‖ := by gcongr
      _ = ‖F s‖ := (norm_mul _ _).symm
      _ ≤ Cb := hPL
  have hCb0 : 0 ≤ Cb := (by positivity : (0:ℝ) ≤ _).trans hFs
  calc ‖riemannZeta₁ s‖ = ‖riemannZeta₁ s‖ * (x ^ (-(α + β * σ) / 2) * Real.exp (-B₀)) *
        (x ^ ((α + β * σ) / 2) * Real.exp B₀) := by
        rw [show ‖riemannZeta₁ s‖ * (x ^ (-(α + β * σ) / 2) * Real.exp (-B₀)) *
          (x ^ ((α + β * σ) / 2) * Real.exp B₀) = ‖riemannZeta₁ s‖ *
          (x ^ (-(α + β * σ) / 2) * x ^ ((α + β * σ) / 2)) * (Real.exp (-B₀) * Real.exp B₀) by ring,
          hcancel, ← Real.exp_add]; simp
    _ ≤ Cb * (x ^ ((α + β * σ) / 2) * Real.exp B₀) := by gcongr
    _ ≤ Cb * (max 1 ((2 * K) ^ ((α + β * σ) / 2)) * (1 + t ^ 2) ^ ((α + β * σ) / 2) *
          Real.exp B₀) := by gcongr
    _ = Cb * max 1 ((2 * K) ^ ((α + β * σ) / 2)) * Real.exp B₀ *
          (1 + t ^ 2) ^ ((α + β * σ) / 2) := by ring

lemma norm_cos_le_exp (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  rw [Complex.cos]
  have h1 : ‖Complex.exp (-z * I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr (by simp; exact le_abs_self _)
  have h2 : ‖Complex.exp (z * I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr (by simp; exact neg_le_abs _)
  calc ‖(Complex.exp (z * I) + Complex.exp (-z * I)) / 2‖
      = ‖Complex.exp (z * I) + Complex.exp (-z * I)‖ / 2 := by simp
    _ ≤ (‖Complex.exp (z * I)‖ + ‖Complex.exp (-z * I)‖) / 2 := by
        gcongr; exact norm_add_le _ _
    _ ≤ Real.exp |z.im| := by linarith

lemma exp_abs_le_two_cosh (x : ℝ) : Real.exp |x| ≤ 2 * Real.cosh x := by
  rw [Real.cosh_eq]
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]; linarith [Real.exp_pos (-x)]
  · rw [abs_of_nonpos h]; linarith [Real.exp_pos x]

/-- `|Γ(1/2+it)|² cosh(πt) = π`. -/
lemma norm_Gamma_half_sq (t : ℝ) :
    ‖Complex.Gamma (1 / 2 + t * I)‖ ^ 2 * Real.cosh (π * t) = π := by
  have h := Complex.Gamma_mul_Gamma_one_sub (1 / 2 + t * I)
  have h1 : 1 - (1 / 2 + t * I) = conj (1 / 2 + t * I) := by
    apply Complex.ext <;> simp; norm_num
  rw [h1, Complex.Gamma_conj, Complex.mul_conj] at h
  have h2 : Complex.sin (π * (1 / 2 + t * I)) = (Real.cosh (π * t) : ℂ) := by
    rw [show (π : ℂ) * (1 / 2 + t * I) = ((π * t : ℝ) : ℂ) * I + π / 2 by push_cast; ring,
      Complex.sin_add_pi_div_two, Complex.cos_mul_I, Complex.ofReal_cosh]
  rw [h2] at h
  have hc : 0 < Real.cosh (π * t) := Real.cosh_pos _
  have h3 : Complex.normSq (Complex.Gamma (1 / 2 + t * I)) = π / Real.cosh (π * t) := by
    exact_mod_cast h
  rw [← Complex.normSq_eq_norm_sq, h3]
  field_simp

lemma norm_Gamma_half_mul_cosh_le (t : ℝ) :
    ‖Complex.Gamma (1 / 2 + t * I)‖ * Real.cosh (π * t / 2) ≤ 2 := by
  have h := norm_Gamma_half_sq t
  have hc2 : Real.cosh (π * t / 2) ^ 2 ≤ Real.cosh (π * t) := by
    have := Real.cosh_two_mul (π * t / 2)
    rw [show 2 * (π * t / 2) = π * t by ring] at this
    have h1 := Real.cosh_sq (π * t / 2)
    have h2 := Real.one_le_cosh (π * t / 2)
    nlinarith
  have hx : 0 ≤ ‖Complex.Gamma (1 / 2 + t * I)‖ * Real.cosh (π * t / 2) :=
    mul_nonneg (norm_nonneg _) (Real.cosh_pos _).le
  have hsq : (‖Complex.Gamma (1 / 2 + t * I)‖ * Real.cosh (π * t / 2)) ^ 2 ≤ 4 := by
    rw [mul_pow]
    calc ‖Complex.Gamma (1 / 2 + t * I)‖ ^ 2 * Real.cosh (π * t / 2) ^ 2
        ≤ ‖Complex.Gamma (1 / 2 + t * I)‖ ^ 2 * Real.cosh (π * t) := by gcongr
      _ = π := h
      _ ≤ 4 := Real.pi_le_four
  nlinarith

lemma norm_Gamma_half_add_nat_le (t : ℝ) (n : ℕ) :
    ‖Complex.Gamma (1 / 2 + n + t * I)‖ ≤ ‖Complex.Gamma (1 / 2 + t * I)‖ * (n + 1 + |t|) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hne : (1 / 2 + n + t * I : ℂ) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    rw [show (1 / 2 + ((n + 1 : ℕ) : ℂ) + t * I) = (1 / 2 + n + t * I) + 1 by push_cast; ring,
      Complex.Gamma_add_one _ hne, norm_mul]
    have hn : ‖(1 / 2 + n + t * I : ℂ)‖ ≤ (n : ℝ) + 2 + |t| := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      simp
      rw [abs_of_nonneg (by positivity)]
      linarith
    have hG := norm_nonneg (Complex.Gamma (1 / 2 + t * I))
    calc ‖(1 / 2 + n + t * I : ℂ)‖ * ‖Complex.Gamma (1 / 2 + n + t * I)‖
        ≤ ((n : ℝ) + 2 + |t|) * (‖Complex.Gamma (1 / 2 + t * I)‖ * (n + 1 + |t|) ^ n) := by
          gcongr
      _ ≤ ((n : ℝ) + 2 + |t|) * (‖Complex.Gamma (1 / 2 + t * I)‖ * (n + 2 + |t|) ^ n) := by
          gcongr; linarith
      _ = ‖Complex.Gamma (1 / 2 + t * I)‖ * (((n + 1 : ℕ) : ℝ) + 1 + |t|) ^ (n + 1) := by
          push_cast; ring

/-- On the line `Re w = 1/2 + n`: `‖Γ(w) cos(πw/2)‖ ≤ 4 (n + 1 + |t|)^n`. -/
lemma norm_Gamma_mul_cos_le (t : ℝ) (n : ℕ) :
    ‖Complex.Gamma (1 / 2 + n + t * I) * Complex.cos (π * (1 / 2 + n + t * I) / 2)‖ ≤
      4 * (n + 1 + |t|) ^ n := by
  rw [norm_mul]
  have hcos : ‖Complex.cos (π * (1 / 2 + n + t * I) / 2)‖ ≤ 2 * Real.cosh (π * t / 2) := by
    refine (norm_cos_le_exp _).trans ((le_of_eq ?_).trans (exp_abs_le_two_cosh (π * t / 2)))
    congr 2; simp
  have h1 := norm_Gamma_half_add_nat_le t n
  have h2 := norm_Gamma_half_mul_cosh_le t
  have hp : 0 ≤ ((n : ℝ) + 1 + |t|) ^ n := by positivity
  calc ‖Complex.Gamma (1 / 2 + n + t * I)‖ * ‖Complex.cos (π * (1 / 2 + n + t * I) / 2)‖
      ≤ (‖Complex.Gamma (1 / 2 + t * I)‖ * (n + 1 + |t|) ^ n) * (2 * Real.cosh (π * t / 2)) := by
        gcongr
    _ = 2 * (‖Complex.Gamma (1 / 2 + t * I)‖ * Real.cosh (π * t / 2)) * (n + 1 + |t|) ^ n := by
        ring
    _ ≤ 2 * 2 * (n + 1 + |t|) ^ n := by gcongr
    _ = 4 * (n + 1 + |t|) ^ n := by ring

lemma one_add_abs_le_two_sqrt (u : ℝ) : 1 + |u| ≤ 2 * Real.sqrt (1 + u ^ 2) := by
  have h1 : 1 ≤ Real.sqrt (1 + u ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg u])
  have h2 : |u| ≤ Real.sqrt (1 + u ^ 2) := Real.abs_le_sqrt (by linarith)
  linarith

lemma one_add_abs_pow_le (u : ℝ) (k : ℕ) :
    (1 + |u|) ^ k ≤ 2 ^ k * (1 + u ^ 2) ^ ((k : ℝ) / 2) := by
  calc (1 + |u|) ^ k ≤ (2 * Real.sqrt (1 + u ^ 2)) ^ k :=
        pow_le_pow_left₀ (by positivity) (one_add_abs_le_two_sqrt u) k
    _ = 2 ^ k * (1 + u ^ 2) ^ ((k : ℝ) / 2) := by
        rw [mul_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast (_ ^ _), ← Real.rpow_mul (by positivity)]
        ring_nf

/-- Polynomial bound for `ζ` on the line `Re s = 1/2 - n`, `n ≥ 1`, from the functional equation. -/
lemma zeta_left_line (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, ∀ u : ℝ, ‖riemannZeta (((1 / 2 - n : ℝ) : ℂ) + u * I)‖ ≤ C * (n + 1 + |u|) ^ n := by
  obtain ⟨C₀, hC₀⟩ := exists_norm_riemannZeta_le (σ := 3/2) (by norm_num)
  refine ⟨8 * C₀, fun u => ?_⟩
  set w : ℂ := 1 / 2 + n + (-u : ℝ) * I with hw
  have hwre : w.re = 1 / 2 + n := by simp [hw]
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have h1w : ((1 / 2 - n : ℝ) : ℂ) + u * I = 1 - w := by rw [hw]; push_cast; ring
  have hw0 : ∀ m : ℕ, w ≠ -m := by
    intro m h; have := congrArg Complex.re h; rw [hwre] at this; simp at this
    have : (0:ℝ) ≤ m := m.cast_nonneg
    linarith
  have hw1 : w ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hwre] at this; simp at this; linarith
  rw [h1w, riemannZeta_one_sub hw0 hw1,
    show 2 * (2 * (π:ℂ)) ^ (-w) * Complex.Gamma w * Complex.cos (π * w / 2) * riemannZeta w =
      2 * (2 * (π:ℂ)) ^ (-w) * (Complex.Gamma w * Complex.cos (π * w / 2)) * riemannZeta w by ring,
    norm_mul, norm_mul, norm_mul]
  have hpow : ‖(2 * (π:ℂ)) ^ (-w)‖ ≤ 1 := by
    rw [show (2 * (π:ℂ)) = ((2 * π : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
    simp [hwre]; linarith
  have hGc : ‖Complex.Gamma w * Complex.cos (π * w / 2)‖ ≤ 4 * (n + 1 + |u|) ^ n := by
    have := norm_Gamma_mul_cos_le (-u) n
    rw [abs_neg] at this
    exact this
  have hz : ‖riemannZeta w‖ ≤ C₀ := hC₀ w (by rw [hwre]; linarith)
  have hC0 : 0 ≤ C₀ := (norm_nonneg _).trans hz
  calc ‖(2:ℂ)‖ * ‖(2 * (π:ℂ)) ^ (-w)‖ * ‖Complex.Gamma w * Complex.cos (π * w / 2)‖ *
        ‖riemannZeta w‖ ≤ 2 * 1 * (4 * (n + 1 + |u|) ^ n) * C₀ := by
        rw [Complex.norm_two]; gcongr
    _ = 8 * C₀ * (n + 1 + |u|) ^ n := by ring

lemma E_left_line (n : ℕ) (hn : 1 ≤ n) : E (1 / 2 - n) (n + 1) := by
  obtain ⟨C, hC⟩ := zeta_left_line n hn
  refine ⟨C * ((n + 1) ^ (n + 1) * 2 ^ (n + 1)), fun u => ?_⟩
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  set s : ℂ := ((1 / 2 - n : ℝ) : ℂ) + u * I with hs
  have hsre : s.re = 1 / 2 - n := by simp [hs]
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hsre] at this; simp at this; linarith
  have hcast : ((1 / 2 - n : ℝ) : ℂ) = 1 / 2 - (n : ℂ) := by push_cast; ring
  rw [H_eq hs1, norm_mul]
  have hs1n : ‖s - 1‖ ≤ n + 1 + |u| := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp [hs]
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hz := hC u
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans hz
    exact nonneg_of_mul_nonneg_left this (by positivity)
  have hk := one_add_abs_pow_le u (n + 1)
  push_cast at hk
  have hnu : (n : ℝ) + 1 + |u| ≤ (n + 1) * (1 + |u|) := by nlinarith [abs_nonneg u]
  calc ‖s - 1‖ * ‖riemannZeta s‖ ≤ (n + 1 + |u|) * (C * (n + 1 + |u|) ^ n) := by gcongr
    _ = C * (n + 1 + |u|) ^ (n + 1) := by ring
    _ ≤ C * (((n:ℝ) + 1) * (1 + |u|)) ^ (n + 1) := by gcongr
    _ = C * ((n + 1) ^ (n + 1) * (1 + |u|) ^ (n + 1)) := by rw [mul_pow]
    _ ≤ C * ((n + 1) ^ (n + 1) * (2 ^ (n + 1) * (1 + u ^ 2) ^ (((n:ℝ) + 1) / 2))) := by
        gcongr
    _ = C * ((n + 1) ^ (n + 1) * 2 ^ (n + 1)) * (1 + u ^ 2) ^ (((n:ℝ) + 1) / 2) := by ring

/-! ## Comparisons of `|t|^e` with `(1+t²)^(e/2)` -/

lemma sq_rpow_half {t e : ℝ} : (t ^ 2) ^ (e / 2) = |t| ^ e := by
  rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg t)]
  congr 1; push_cast; ring

lemma exists_one_add_sq_rpow_le (e : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 1 ≤ |t| → (1 + t ^ 2) ^ (e / 2) ≤ K * |t| ^ e := by
  refine ⟨max 1 (2 ^ (e / 2)), by positivity, fun t ht => ?_⟩
  have ht2 : 1 ≤ t ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
  have := rpow_le_max_mul (e := e / 2) (x := 1 + t ^ 2) (y := t ^ 2) (c := 2) (by linarith)
    (by linarith) (by linarith)
  rwa [sq_rpow_half] at this

lemma exists_rpow_le_one_add_sq (e : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 1 ≤ |t| → |t| ^ e ≤ K * (1 + t ^ 2) ^ (e / 2) := by
  refine ⟨max 1 (2 ^ (e / 2)) / 2 ^ (e / 2), by positivity, fun t ht => ?_⟩
  have ht2 : 1 ≤ t ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
  have := rpow_le_max_mul (e := e / 2) (x := t ^ 2) (y := (1 + t ^ 2) / 2) (c := 2) (by positivity)
    (by linarith) (by linarith)
  rw [sq_rpow_half, Real.div_rpow (by positivity) (by norm_num)] at this
  calc |t| ^ e ≤ max 1 (2 ^ (e / 2)) * ((1 + t ^ 2) ^ (e / 2) / 2 ^ (e / 2)) := this
    _ = max 1 (2 ^ (e / 2)) / 2 ^ (e / 2) * (1 + t ^ 2) ^ (e / 2) := by ring

/-! ## Conversions between `O(T^a)` on a line and `E` -/

lemma norm_zeta_neg (σ t : ℝ) :
    ‖riemannZeta (σ + (-t : ℝ) * I)‖ = ‖riemannZeta (σ + t * I)‖ := by
  have h := riemannZeta_conj (σ + t * I)
  have hc : conj ((σ : ℂ) + t * I) = (σ : ℂ) + (-t : ℝ) * I := by
    apply Complex.ext <;> simp
  rw [hc] at h
  rw [h, Complex.norm_conj]

theorem E_of_isBigO {σ a : ℝ}
    (h : (fun T : ℝ => riemannZeta (σ + T * I)) =O[atTop] (fun T : ℝ => T ^ a)) :
    E σ (a + 1) := by
  obtain ⟨C, hC⟩ := h.bound
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hC
  set T₁ := max T₀ 1 with hT₁
  have hT₁1 : 1 ≤ T₁ := le_max_right _ _
  -- bound on `|t| ≥ T₁`
  have hfar : ∀ t : ℝ, T₁ ≤ |t| → ‖riemannZeta (σ + t * I)‖ ≤ |C| * |t| ^ a := by
    intro t ht
    have key : ∀ u : ℝ, T₁ ≤ u → ‖riemannZeta (σ + u * I)‖ ≤ |C| * u ^ a := by
      intro u hu
      have hu0 : 0 ≤ u := by linarith
      have := hT₀ u (le_trans (le_max_left _ _) hu)
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hu0 _)] at this
      exact this.trans (by gcongr; exact le_abs_self C)
    rcases le_total 0 t with h0 | h0
    · rw [abs_of_nonneg h0] at ht ⊢; exact key t ht
    · rw [abs_of_nonpos h0] at ht ⊢
      rw [← norm_zeta_neg]; exact key (-t) ht
  obtain ⟨K₁, hK₁, hK₁t⟩ := exists_rpow_le_one_add_sq (a + 1)
  -- compact part
  have hcont : Continuous (fun t : ℝ =>
      ‖riemannZeta₁ (σ + t * I)‖ / (1 + t ^ 2) ^ ((a + 1) / 2)) := by
    refine Continuous.div ?_ ?_ (fun t => (Real.rpow_pos_of_pos (by positivity) _).ne')
    · exact (differentiable_riemannZeta₁.continuous.comp (by fun_prop)).norm
    · exact Continuous.rpow_const (by fun_prop) (fun t => Or.inl (by positivity))
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -T₁) (b := T₁)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max M ((|σ - 1| + 1) * |C| * K₁), fun t => ?_⟩
  have hpos : 0 < (1 + t ^ 2) ^ ((a + 1) / 2) := Real.rpow_pos_of_pos (by positivity) _
  rcases le_or_gt T₁ |t| with ht | ht
  · have ht1 : 1 ≤ |t| := hT₁1.trans ht
    have hs1 : (σ : ℂ) + t * I ≠ 1 := by
      intro h; have := congrArg Complex.im h; simp at this; rw [this] at ht1; simp at ht1
      linarith
    rw [H_eq hs1, norm_mul]
    have hn : ‖(σ : ℂ) + t * I - 1‖ ≤ (|σ - 1| + 1) * |t| := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      simp
      nlinarith [abs_nonneg (σ - 1)]
    have hz := hfar t ht
    calc ‖(σ : ℂ) + t * I - 1‖ * ‖riemannZeta (σ + t * I)‖
        ≤ ((|σ - 1| + 1) * |t|) * (|C| * |t| ^ a) := by gcongr
      _ = (|σ - 1| + 1) * |C| * |t| ^ (a + 1) := by
          rw [Real.rpow_add_one (by positivity : |t| ≠ 0)]; ring
      _ ≤ (|σ - 1| + 1) * |C| * (K₁ * (1 + t ^ 2) ^ ((a + 1) / 2)) := by
          gcongr; exact hK₁t t ht1
      _ ≤ max M ((|σ - 1| + 1) * |C| * K₁) * (1 + t ^ 2) ^ ((a + 1) / 2) := by
          rw [← mul_assoc]; gcongr; exact le_max_right _ _
  · have htI : t ∈ Icc (-T₁) T₁ := ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
    have := hM t htI
    rw [Real.norm_of_nonneg (by positivity), div_le_iff₀ hpos] at this
    exact this.trans (by gcongr; exact le_max_left _ _)

theorem isBigO_of_E {σ e : ℝ} (h : E σ e) :
    (fun T : ℝ => riemannZeta (σ + T * I)) =O[atTop] (fun T : ℝ => T ^ (e - 1)) := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨K, hK, hKt⟩ := exists_one_add_sq_rpow_le e
  refine IsBigO.of_bound (|C| * K) ?_
  filter_upwards [eventually_ge_atTop 1] with T hT
  have hT0 : 0 < T := by linarith
  have hs1 : (σ : ℂ) + T * I ≠ 1 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have hH := hC T
  rw [H_eq hs1, norm_mul] at hH
  have hn : T ≤ ‖(σ : ℂ) + T * I - 1‖ := by
    refine le_trans (le_of_eq ?_) (Complex.abs_im_le_norm _); simp; exact (abs_of_pos hT0).symm
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hT0.le _)]
  have hTe := hKt T (by rw [abs_of_pos hT0]; exact hT)
  rw [abs_of_pos hT0] at hTe
  have h1 : T * ‖riemannZeta (σ + T * I)‖ ≤ |C| * (K * T ^ e) := by
    calc T * ‖riemannZeta (σ + T * I)‖ ≤ ‖(σ : ℂ) + T * I - 1‖ * ‖riemannZeta (σ + T * I)‖ := by
          gcongr
      _ ≤ C * (1 + T ^ 2) ^ (e / 2) := hH
      _ ≤ |C| * (1 + T ^ 2) ^ (e / 2) := by gcongr; exact le_abs_self C
      _ ≤ |C| * (K * T ^ e) := by gcongr
  rw [Real.rpow_sub_one hT0.ne', mul_div_assoc', le_div_iff₀ hT0]
  linarith

/-! ## Assembly -/

/-- Admissible exponents on the line `Re s = σ`. -/
def S (σ : ℝ) : Set ℝ :=
  {a : ℝ | (fun T : ℝ => riemannZeta (σ + T * I)) =O[atTop] (fun T : ℝ => T ^ a)}

theorem S_interp {σ₁ σ₂ a₁ a₂ : ℝ} (h12 : σ₁ < σ₂) (h1 : a₁ ∈ S σ₁) (h2 : a₂ ∈ S σ₂) {σ : ℝ}
    (hσ1 : σ₁ ≤ σ) (hσ2 : σ ≤ σ₂) : a₁ + (σ - σ₁) / (σ₂ - σ₁) * (a₂ - a₁) ∈ S σ := by
  have h := isBigO_of_E (E_interp h12 (E_of_isBigO h1) (E_of_isBigO h2) hσ1 hσ2)
  have heq : a₁ + 1 + (σ - σ₁) / (σ₂ - σ₁) * (a₂ + 1 - (a₁ + 1)) - 1 =
      a₁ + (σ - σ₁) / (σ₂ - σ₁) * (a₂ - a₁) := by ring
  rw [heq] at h
  exact h

theorem S_nonempty (σ : ℝ) : ∃ a, a ∈ S σ := by
  rcases lt_or_ge 1 σ with h | h
  · exact ⟨0, isBigO_rpow_zero_of_one_lt h⟩
  · set n : ℕ := ⌈|σ|⌉₊ + 1 with hn
    have hn1 : 1 ≤ n := by omega
    have hceil : |σ| ≤ (⌈|σ|⌉₊ : ℝ) := Nat.le_ceil _
    have hnr : (n : ℝ) = ⌈|σ|⌉₊ + 1 := by rw [hn]; push_cast; ring
    have hσn : (1 / 2 - n : ℝ) < σ := by
      rw [hnr]; linarith [neg_abs_le σ]
    have h2 : E 2 1 := by
      have := E_of_isBigO (isBigO_rpow_zero_of_one_lt (σ := 2) (by norm_num))
      simpa using this
    have := E_interp (by linarith) (E_left_line n hn1) h2 hσn.le (by linarith)
    exact ⟨_, isBigO_of_E this⟩

theorem mu_ne_top (σ : ℝ) : mu σ ≠ ⊤ := by
  obtain ⟨a, ha⟩ := S_nonempty σ
  exact ne_top_of_le_ne_top (EReal.coe_ne_top a) (mu_le_of_isBigO ha)

theorem mu_ne_bot (σ : ℝ) : mu σ ≠ ⊥ := by
  intro hbot
  rcases lt_or_ge 1 σ with h | h
  · rw [mu_eq_zero_of_one_lt σ h] at hbot; exact EReal.zero_ne_bot hbot
  · have hb : -(3 - σ) ∈ S σ := isBigO_of_mu_lt (by rw [hbot]; exact EReal.bot_lt_coe _)
    have h0 : (0:ℝ) ∈ S 3 := isBigO_rpow_zero_of_one_lt (by norm_num)
    have hi := S_interp (σ₁ := σ) (σ₂ := 3) (by linarith) hb h0 (σ := 2) (by linarith)
      (by norm_num)
    have hd : (3 - σ) ≠ 0 := by linarith
    have heq : -(3 - σ) + (2 - σ) / (3 - σ) * (0 - -(3 - σ)) = -1 := by
      field_simp; ring
    rw [heq] at hi
    have h1 := mu_le_of_isBigO hi
    rw [mu_eq_zero_of_one_lt 2 (by norm_num)] at h1
    have : (0:ℝ) ≤ -1 := by exact_mod_cast h1
    linarith

/-- The real-valued `μ`. -/
noncomputable def muR (σ : ℝ) : ℝ := (mu σ).toReal

theorem mu_eq_muR (σ : ℝ) : mu σ = (muR σ : EReal) :=
  (EReal.coe_toReal (mu_ne_top σ) (mu_ne_bot σ)).symm

theorem muR_le_of_mem {σ a : ℝ} (h : a ∈ S σ) : muR σ ≤ a := by
  have := mu_le_of_isBigO h
  rw [mu_eq_muR] at this
  exact_mod_cast this

theorem mem_of_muR_lt {σ a : ℝ} (h : muR σ < a) : a ∈ S σ :=
  isBigO_of_mu_lt (by rw [mu_eq_muR]; exact_mod_cast h)

theorem muR_interp {x y : ℝ} (hxy : x < y) {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    muR (x + b * (y - x)) ≤ muR x + b * (muR y - muR x) := by
  apply le_of_forall_pos_lt_add
  intro ε hε
  have h1 : muR x + ε / 2 ∈ S x := mem_of_muR_lt (by linarith)
  have h2 : muR y + ε / 2 ∈ S y := mem_of_muR_lt (by linarith)
  have hd : 0 < y - x := sub_pos.mpr hxy
  have hi := S_interp hxy h1 h2 (σ := x + b * (y - x)) (by nlinarith) (by nlinarith)
  have heq : (muR x + ε / 2) + (x + b * (y - x) - x) / (y - x) *
      ((muR y + ε / 2) - (muR x + ε / 2)) = muR x + b * (muR y - muR x) + ε / 2 := by
    field_simp; ring
  rw [heq] at hi
  have := muR_le_of_mem hi
  linarith

theorem muR_convex : ConvexOn ℝ univ muR := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have ha' : a = 1 - b := by linarith
  subst ha'
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · have := muR_interp hxy hb (by linarith)
    rw [show (1 - b) * x + b * y = x + b * (y - x) by ring]
    linarith
  · rw [show (1 - b) * x + b * x = x by ring]; linarith
  · have := muR_interp hxy ha (by linarith)
    rw [show (1 - b) * x + b * y = y + (1 - b) * (x - y) by ring]
    linarith

theorem mu_convex' : ∃ f : ℝ → ℝ, ConvexOn ℝ Set.univ f ∧ ∀ σ : ℝ, mu σ = (f σ : EReal) :=
  ⟨muR, muR_convex, mu_eq_muR⟩

end LindelofHypothesis.LHD

open LindelofHypothesis in
theorem solution :
    ∃ f : ℝ → ℝ, ConvexOn ℝ Set.univ f ∧ ∀ σ : ℝ, mu σ = (f σ : EReal) :=
  LHD.mu_convex'
