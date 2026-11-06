-- Prove2me | solution 1 for GuthMaynard.norm_dyadic_sum_cpow_le_dual_sum
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T23:26:19.267393+00:00
-- url     : https://prove2.me/submissions/22e6b0fb-1014-4e8d-addc-465244ed2766

import Mathlib

section
open Complex Real MeasureTheory intervalIntegral Finset
namespace GuthMaynard.BProc
/-!
Blueprint: Kerr's Lemma 26 (van der Corput's B-process for `∑_{N ≤ n ≤ 2N} n^{it}`),
`GuthMaynard.norm_dyadic_sum_cpow_le_dual_sum`, by an elementary route:

* Euler–Maclaurin (first order) on `(a, b] = (N-1, 2N]` for `F(x) = x^{it}`;
* the sawtooth `ψ` written as its Fourier polynomial of degree `K` plus a remainder `sawTail K`
  whose `L¹` norm on a unit interval is `≤ 1/√K` (orthogonality + `∑ 1/μ² = π²/6`);
* so the sum is `∑_{|ν| ≤ K} ∫_a^b x^{it} e(-νx) dx` up to `O(1)`;
* the first- and second-derivative tests for `∫ e^{i(t log x - c x)}` bound the
  non-stationary `ν`;
* for stationary `ν`, `x = y/ν` gives `ν^{-1-it} ∫_{νa}^{νb} e^{i(t log y - 2π y)} dy`, which is
  `ν^{-1-it} G(A,B)` up to tails, with `G(A,B) = O(√t)` independent of `ν`;
* Abel summation with the decreasing weights `1/ν`.
-/
/-- The oscillatory integrand `e^{i(t log x - c x)}`. -/
noncomputable def ph (t c x : ℝ) : ℂ :=
  Complex.exp (((t * Real.log x - c * x : ℝ) : ℂ) * Complex.I)

/-- `∫_u^v e^{i(t log x - c x)} dx`. -/
noncomputable def phaseInt (t c u v : ℝ) : ℂ := ∫ x in u..v, ph t c x

/-- The sawtooth `ψ(x) = x - ⌊x⌋ - 1/2`. -/
noncomputable def saw (x : ℝ) : ℝ := x - ⌊x⌋ - 1 / 2

/-- `ψ(x) + ∑_{1 ≤ |μ| ≤ K} e(μx)/(2πiμ)`, the remainder of the degree-`K` Fourier polynomial. -/
noncomputable def sawTail (K : ℕ) (x : ℝ) : ℂ :=
  (saw x : ℂ) + ∑ μ ∈ (Finset.Icc (-(K : ℤ)) K).erase 0,
    Complex.exp (2 * π * (μ : ℂ) * (x : ℂ) * I) / (2 * π * (μ : ℂ) * I)

end GuthMaynard.BProc
end

section
open Complex Real MeasureTheory intervalIntegral Finset
namespace GuthMaynard.BProc.PartA
open GuthMaynard.BProc
lemma norm_ph (t c x : ℝ) : ‖ph t c x‖ = 1 := by
  unfold ph
  exact Complex.norm_exp_ofReal_mul_I _

lemma hasDerivAt_ph (t c x : ℝ) (hx : 0 < x) :
    HasDerivAt (ph t c) (((t / x - c : ℝ) : ℂ) * I * ph t c x) x := by
  have h1 : HasDerivAt (fun y => t * Real.log y - c * y) (t * x⁻¹ - c) x := by
    have := ((Real.hasDerivAt_log hx.ne').const_mul t).sub ((hasDerivAt_id x).const_mul c)
    exact this.congr_deriv (by simp)
  have h2 := (h1.ofReal_comp.mul_const I).cexp
  have hph : ph t c = fun x => Complex.exp (((t * Real.log x - c * x : ℝ) : ℂ) * I) := rfl
  rw [hph]
  convert h2 using 1
  push_cast
  ring

lemma ph_intervalIntegrable (t c u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    IntervalIntegrable (ph t c) volume u v := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_of_forall_continuousAt
  intro x hx
  have : 0 < x := by
    rcases Set.mem_uIcc.mp hx with h | h <;> linarith [h.1]
  exact (hasDerivAt_ph t c x this).continuousAt

lemma phaseInt_split (t c u w v : ℝ) (hu : 0 < u) (hw : 0 < w) (hv : 0 < v) :
    phaseInt t c u v = phaseInt t c u w + phaseInt t c w v := by
  unfold phaseInt
  rw [integral_add_adjacent_intervals (ph_intervalIntegrable t c u w hu hw)
    (ph_intervalIntegrable t c w v hw hv)]

lemma phaseInt_trivial (t c u v : ℝ) (huv : u ≤ v) : ‖phaseInt t c u v‖ ≤ v - u := by
  unfold phaseInt
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := u) (b := v) (C := 1)
    (f := ph t c) (fun x _ => (norm_ph t c x).le)
  rw [abs_of_nonneg (by linarith)] at this
  linarith

/-- The derivative of `1/φ'`. -/
lemma hasDerivAt_inv_phase (t c x : ℝ) (hx : 0 < x) (hne : t / x - c ≠ 0) :
    HasDerivAt (fun y => (t / y - c)⁻¹) (t / x ^ 2 / (t / x - c) ^ 2) x := by
  have h1 : HasDerivAt (fun y => t / y - c) (-(t / x ^ 2)) x := by
    have := ((hasDerivAt_inv hx.ne').const_mul t).sub_const c
    have e : (fun y => t / y - c) = (fun y => t * y⁻¹ - c) := by funext y; ring
    rw [e]
    exact this.congr_deriv (by ring)
  exact (h1.inv hne).congr_deriv (by ring)

theorem fd_bound (t c u v m : ℝ) (ht : 0 < t) (hu : 0 < u) (huv : u ≤ v) (hm : 0 < m)
    (h : m ≤ t / v - c ∨ t / u - c ≤ -m) : ‖phaseInt t c u v‖ ≤ 4 / m := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have hpos : ∀ x ∈ Set.uIcc u v, 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le huv] at hx
    linarith [hx.1]
  -- |φ'| ≥ m on [u,v]
  have hbig : ∀ x ∈ Set.uIcc u v, m ≤ |t / x - c| := by
    intro x hx
    have hx0 := hpos x hx
    rw [Set.uIcc_of_le huv] at hx
    rcases h with h | h
    · have : t / v ≤ t / x := div_le_div_of_nonneg_left ht.le hx0 hx.2
      rw [abs_of_pos (by linarith)]
      linarith
    · have : t / x ≤ t / u := div_le_div_of_nonneg_left ht.le hu hx.1
      rw [abs_of_neg (by linarith)]
      linarith
  have hne : ∀ x ∈ Set.uIcc u v, t / x - c ≠ 0 := by
    intro x hx h0
    have := hbig x hx
    rw [h0, abs_zero] at this
    linarith
  have hinvle : ∀ x ∈ Set.uIcc u v, |(t / x - c)⁻¹| ≤ 1 / m := by
    intro x hx
    rw [abs_inv, one_div]
    exact inv_anti₀ hm (hbig x hx)
  set U : ℝ → ℂ := fun x => -I * (((t / x - c)⁻¹ : ℝ) : ℂ) with hU
  set hd : ℝ → ℝ := fun x => t / x ^ 2 / (t / x - c) ^ 2 with hhd
  set U' : ℝ → ℂ := fun x => -I * ((hd x : ℝ) : ℂ) with hU'
  set V' : ℝ → ℂ := fun x => ((t / x - c : ℝ) : ℂ) * I * ph t c x with hV'
  have hUd : ∀ x ∈ Set.uIcc u v, HasDerivAt U (U' x) x := by
    intro x hx
    have := (hasDerivAt_inv_phase t c x (hpos x hx) (hne x hx)).ofReal_comp.const_mul (-I)
    simpa [hU, hU', hhd] using this
  have hVd : ∀ x ∈ Set.uIcc u v, HasDerivAt (ph t c) (V' x) x :=
    fun x hx => hasDerivAt_ph t c x (hpos x hx)
  have hhd_cont : ContinuousOn hd (Set.uIcc u v) := by
    apply continuousOn_of_forall_continuousAt
    intro x hx
    have hx0 := (hpos x hx).ne'
    have hn := hne x hx
    have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx0
    have hn2 : (t / x - c) ^ 2 ≠ 0 := pow_ne_zero 2 hn
    simp only [hhd]
    fun_prop (disch := assumption)
  have hU'int : IntervalIntegrable U' volume u v := by
    apply ContinuousOn.intervalIntegrable
    simp only [hU']
    exact continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hhd_cont)
  have hV'int : IntervalIntegrable V' volume u v := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro x hx
    have hx0 := (hpos x hx).ne'
    have hc : ContinuousAt (fun y : ℝ => ((t / y - c : ℝ) : ℂ) * I) x := by
      apply ContinuousAt.mul _ continuousAt_const
      exact Complex.continuous_ofReal.continuousAt.comp (by fun_prop (disch := assumption))
    exact hc.mul (hasDerivAt_ph t c x (hpos x hx)).continuousAt
  have hparts := integral_mul_deriv_eq_deriv_mul hUd hVd hU'int hV'int
  have hint_eq : (∫ x in u..v, U x * V' x) = phaseInt t c u v := by
    unfold phaseInt
    apply integral_congr
    intro x hx
    have hn := hne x hx
    simp only [hU, hV']
    have hn' : ((t / x - c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn
    push_cast
    push_cast at hn'
    field_simp
    rw [I_sq]
    ring
  rw [hint_eq] at hparts
  rw [hparts]
  -- the remaining integral
  have hFTC : (∫ x in u..v, hd x) = (t / v - c)⁻¹ - (t / u - c)⁻¹ :=
    integral_eq_sub_of_hasDerivAt
      (fun x hx => hasDerivAt_inv_phase t c x (hpos x hx) (hne x hx))
      (hhd_cont.intervalIntegrable)
  have hrem : ‖∫ x in u..v, U' x * ph t c x‖ ≤ 2 / m := by
    have := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (f := fun x => U' x * ph t c x)
      (g := hd) huv (Filter.Eventually.of_forall (fun x _ => by
        have h0 : 0 ≤ hd x := by simp only [hhd]; positivity
        simp only [hU', norm_mul, norm_ph, norm_neg, Complex.norm_I, Complex.norm_real,
          Real.norm_eq_abs, one_mul, mul_one]
        rw [abs_of_nonneg h0]))
      hhd_cont.intervalIntegrable
    rw [hFTC] at this
    have h1 := hinvle v Set.right_mem_uIcc
    have h2 := hinvle u Set.left_mem_uIcc
    have h3 : (t / v - c)⁻¹ - (t / u - c)⁻¹ ≤ |(t / v - c)⁻¹| + |(t / u - c)⁻¹| := by
      have := le_abs_self ((t / v - c)⁻¹)
      have := neg_abs_le ((t / u - c)⁻¹)
      linarith
    have : 2 / m = 1 / m + 1 / m := by ring
    linarith
  have hbd : ∀ x ∈ Set.uIcc u v, ‖U x * ph t c x‖ ≤ 1 / m := by
    intro x hx
    simp only [hU, norm_mul, norm_ph, norm_neg, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, one_mul, mul_one]
    exact hinvle x hx
  calc ‖U v * ph t c v - U u * ph t c u - ∫ x in u..v, U' x * ph t c x‖
      ≤ ‖U v * ph t c v‖ + ‖U u * ph t c u‖ + ‖∫ x in u..v, U' x * ph t c x‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ 1 / m + 1 / m + 2 / m := by
        gcongr
        · exact hbd v Set.right_mem_uIcc
        · exact hbd u Set.left_mem_uIcc
    _ = 4 / m := by ring

end GuthMaynard.BProc.PartA
end

section
open Complex Real MeasureTheory intervalIntegral Finset
namespace GuthMaynard.BProc
/-! ### Part A: derivative tests for the phase `t log x - c x` -/
alias fd_bound := GuthMaynard.BProc.PartA.fd_bound

end GuthMaynard.BProc
end

section
open Complex Real MeasureTheory intervalIntegral Finset
namespace GuthMaynard.BProc.PartA
open GuthMaynard.BProc
/-- A short piece: if `φ'` drops by at most `δ` on `[u, w]`, its length is `≤ δ w² / t`. -/
lemma short_piece (t c u w v δ : ℝ) (ht : 0 < t) (hu : 0 < u) (huw : u ≤ w) (hwv : w ≤ v)
    (hd : t / u - t / w ≤ δ) : ‖phaseInt t c u w‖ ≤ δ * v ^ 2 / t := by
  have hw : 0 < w := lt_of_lt_of_le hu huw
  refine (phaseInt_trivial t c u w huw).trans ?_
  have hδ : 0 ≤ δ := by
    have : t / w ≤ t / u := div_le_div_of_nonneg_left ht.le hu huw
    linarith
  have heq : t / u - t / w = t * (w - u) / (u * w) := by field_simp
  rw [heq, div_le_iff₀ (by positivity)] at hd
  rw [le_div_iff₀ ht]
  have h1 : u * w ≤ v ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h1 hδ]

lemma delta_facts (t v : ℝ) (ht : 0 < t) (hv : 0 < v) :
    0 < 2 * Real.sqrt t / v ∧ 4 / (2 * Real.sqrt t / v) = 2 * v / Real.sqrt t ∧
      (2 * Real.sqrt t / v) * v ^ 2 / t = 2 * v / Real.sqrt t := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hst : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  refine ⟨by positivity, ?_, ?_⟩
  · field_simp; ring
  · field_simp
    linear_combination hst

lemma half_pos_side (t c u v : ℝ) (ht : 0 < t) (hu : 0 < u) (huv : u ≤ v)
    (h0 : 0 ≤ t / v - c) : ‖phaseInt t c u v‖ ≤ 4 * v / Real.sqrt t := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  obtain ⟨hδ, h4, h2⟩ := delta_facts t v ht hv
  set δ := 2 * Real.sqrt t / v with hδdef
  have hq : 0 ≤ 2 * v / Real.sqrt t := by positivity
  have hq2 : 4 * v / Real.sqrt t = 2 * (2 * v / Real.sqrt t) := by ring
  by_cases h1 : δ ≤ t / v - c
  · have := fd_bound t c u v δ ht hu huv hδ (Or.inl h1)
    rw [h4] at this
    linarith
  push Not at h1
  by_cases h2' : t / u - c ≤ δ
  · have := short_piece t c u v v δ ht hu huv le_rfl (by linarith)
    rw [h2] at this
    linarith
  push Not at h2'
  have hcδ : 0 < c + δ := by
    have : 0 < t / v := by positivity
    linarith
  set w := t / (c + δ) with hw
  have hwpos : 0 < w := by positivity
  have htw : t / w = c + δ := by rw [hw]; field_simp
  have huw : u < w := by
    by_contra hcon
    push Not at hcon
    have : t / u ≤ t / w := div_le_div_of_nonneg_left ht.le hwpos hcon
    linarith
  have hwv : w < v := by
    by_contra hcon
    push Not at hcon
    have : t / w ≤ t / v := div_le_div_of_nonneg_left ht.le hv hcon
    linarith
  rw [phaseInt_split t c u w v hu hwpos hv]
  have e1 := fd_bound t c u w δ ht hu huw.le hδ (Or.inl (by rw [htw]; linarith))
  have e2 := short_piece t c w v v δ ht hwpos hwv.le le_rfl (by rw [htw]; linarith)
  rw [h4] at e1
  rw [h2] at e2
  have := norm_add_le (phaseInt t c u w) (phaseInt t c w v)
  linarith

lemma half_neg_side (t c u v : ℝ) (ht : 0 < t) (hu : 0 < u) (huv : u ≤ v)
    (h0 : t / u - c ≤ 0) : ‖phaseInt t c u v‖ ≤ 4 * v / Real.sqrt t := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  obtain ⟨hδ, h4, h2⟩ := delta_facts t v ht hv
  set δ := 2 * Real.sqrt t / v with hδdef
  have hq : 0 ≤ 2 * v / Real.sqrt t := by positivity
  have hq2 : 4 * v / Real.sqrt t = 2 * (2 * v / Real.sqrt t) := by ring
  by_cases h1 : t / u - c ≤ -δ
  · have := fd_bound t c u v δ ht hu huv hδ (Or.inr h1)
    rw [h4] at this
    linarith
  push Not at h1
  by_cases h2' : -δ ≤ t / v - c
  · have := short_piece t c u v v δ ht hu huv le_rfl (by linarith)
    rw [h2] at this
    linarith
  push Not at h2'
  have hcδ : 0 < c - δ := by
    have : 0 < t / v := by positivity
    linarith
  set w := t / (c - δ) with hw
  have hwpos : 0 < w := by positivity
  have htw : t / w = c - δ := by rw [hw]; field_simp
  have huw : u < w := by
    by_contra hcon
    push Not at hcon
    have : t / u ≤ t / w := div_le_div_of_nonneg_left ht.le hwpos hcon
    linarith
  have hwv : w < v := by
    by_contra hcon
    push Not at hcon
    have : t / w ≤ t / v := div_le_div_of_nonneg_left ht.le hv hcon
    linarith
  rw [phaseInt_split t c u w v hu hwpos hv]
  have e1 := short_piece t c u w v δ ht hu huw.le hwv.le (by rw [htw]; linarith)
  have e2 := fd_bound t c w v δ ht hwpos hwv.le hδ (Or.inr (by rw [htw]; linarith))
  rw [h2] at e1
  rw [h4] at e2
  have := norm_add_le (phaseInt t c u w) (phaseInt t c w v)
  linarith

theorem sd_bound (t c u v : ℝ) (ht : 0 < t) (hu : 0 < u) (huv : u ≤ v) :
    ‖phaseInt t c u v‖ ≤ 12 * v / Real.sqrt t := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hq : 0 ≤ 4 * v / Real.sqrt t := by positivity
  have hq3 : 12 * v / Real.sqrt t = 3 * (4 * v / Real.sqrt t) := by ring
  by_cases hA : 0 ≤ t / v - c
  · have := half_pos_side t c u v ht hu huv hA
    linarith
  by_cases hB : t / u - c ≤ 0
  · have := half_neg_side t c u v ht hu huv hB
    linarith
  push Not at hA hB
  have hc : 0 < c := by
    have : 0 < t / v := by positivity
    linarith
  set w := t / c with hw
  have hwpos : 0 < w := by positivity
  have htw : t / w = c := by rw [hw]; field_simp
  have huw : u < w := by
    by_contra hcon
    push Not at hcon
    have : t / u ≤ t / w := div_le_div_of_nonneg_left ht.le hwpos hcon
    linarith
  have hwv : w < v := by
    by_contra hcon
    push Not at hcon
    have : t / w ≤ t / v := div_le_div_of_nonneg_left ht.le hv hcon
    linarith
  rw [phaseInt_split t c u w v hu hwpos hv]
  have e1 := half_pos_side t c u w ht hu huw.le (by rw [htw]; simp)
  have e2 := half_neg_side t c w v ht hwpos hwv.le (by rw [htw]; simp)
  have e3 : 4 * w / Real.sqrt t ≤ 4 * v / Real.sqrt t := by gcongr
  have := norm_add_le (phaseInt t c u w) (phaseInt t c w v)
  linarith

end GuthMaynard.BProc.PartA
end

section
open Complex Real MeasureTheory intervalIntegral Finset
namespace GuthMaynard.BProc
alias sd_bound := GuthMaynard.BProc.PartA.sd_bound

end GuthMaynard.BProc
end

section
open Complex Real MeasureTheory intervalIntegral Finset
namespace GuthMaynard.BProc.PartB
open GuthMaynard.BProc
/-! ### Basic facts -/
lemma hasDerivAt_ph (t c x : ℝ) (hx : 0 < x) :
    HasDerivAt (ph t c) ((((t / x - c : ℝ)) : ℂ) * I * ph t c x) x := by
  have h1 : HasDerivAt (fun y => t * Real.log y - c * y) (t * x⁻¹ - c * 1) x :=
    ((Real.hasDerivAt_log hx.ne').const_mul t).sub ((hasDerivAt_id x).const_mul c)
  have h2 := (h1.ofReal_comp.mul_const I).cexp
  show HasDerivAt (fun y => Complex.exp (((t * Real.log y - c * y : ℝ) : ℂ) * I)) _ x
  convert h2 using 1
  rw [ph, div_eq_mul_inv]; push_cast; ring

lemma hasDerivAt_ph0 (t x : ℝ) (hx : 0 < x) :
    HasDerivAt (ph t 0) (((t / x : ℝ) : ℂ) * I * ph t 0 x) x := by
  have := hasDerivAt_ph t 0 x hx
  simpa using this

lemma norm_ph (t c x : ℝ) : ‖ph t c x‖ = 1 := Complex.norm_exp_ofReal_mul_I _

lemma contOn_ph (t c u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    ContinuousOn (ph t c) (Set.uIcc u v) := by
  intro x hx
  have : 0 < x := lt_of_lt_of_le (lt_min hu hv) hx.1
  exact (hasDerivAt_ph t c x this).continuousAt.continuousWithinAt

lemma contOn_fd (t u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    ContinuousOn (fun x : ℝ => ((t / x : ℝ) : ℂ) * I * ph t 0 x) (Set.uIcc u v) := by
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le (lt_min hu hv) hx.1
  apply ContinuousAt.continuousWithinAt
  have h1 : ContinuousAt (fun x : ℝ => ((t / x : ℝ) : ℂ)) x := by
    fun_prop (disch := exact hx0.ne')
  exact (h1.mul continuousAt_const).mul (hasDerivAt_ph0 t x hx0).continuousAt

lemma ii_bdd {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} (hf : AEStronglyMeasurable f volume)
    {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) (a b : ℝ) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded ?_ hf (M := M)
    (ae_of_all _ (fun x => hM x))
  rw [Set.uIoc, Real.volume_Ioc]; exact ENNReal.ofReal_ne_top

lemma saw_meas : Measurable (fun x => ((saw x : ℝ) : ℂ)) := by unfold saw; fun_prop

lemma norm_saw_le (x : ℝ) : ‖((saw x : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  unfold saw; constructor <;> linarith

lemma ii_saw (a b : ℝ) : IntervalIntegrable (fun x => ((saw x : ℝ) : ℂ)) volume a b :=
  ii_bdd saw_meas.aestronglyMeasurable norm_saw_le a b

lemma ii_saw_fd (t u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    IntervalIntegrable (fun x => ((saw x : ℝ) : ℂ) * (((t / x : ℝ) : ℂ) * I * ph t 0 x))
      volume u v :=
  (ii_saw u v).mul_continuousOn (contOn_fd t u v hu hv)

lemma saw_eq_on (n : ℤ) (x : ℝ) (h1 : (n : ℝ) ≤ x) (h2 : x < n + 1) : saw x = x - n - 1 / 2 := by
  unfold saw; rw [Int.floor_eq_iff.2 ⟨h1, h2⟩]

/-! ### Euler–Maclaurin -/
lemma em_unit (t : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∫ x in (n : ℝ)..(n + 1), ((saw x : ℝ) : ℂ) * (((t / x : ℝ) : ℂ) * I * ph t 0 x) =
      (ph t 0 n + ph t 0 (n + 1)) / 2 - phaseInt t 0 n (n + 1) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hcongr : ∫ x in (n : ℝ)..(n + 1), ((saw x : ℝ) : ℂ) * (((t / x : ℝ) : ℂ) * I * ph t 0 x) =
      ∫ x in (n : ℝ)..(n + 1), ((x : ℂ) - n - 1 / 2) * (((t / x : ℝ) : ℂ) * I * ph t 0 x) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume ((n : ℝ) + 1)] with x hx hmem
    rw [Set.uIoc_of_le (by linarith)] at hmem
    have := saw_eq_on (n : ℤ) x (by exact_mod_cast hmem.1.le)
      (by push_cast; exact lt_of_le_of_ne hmem.2 hx)
    rw [this]; push_cast; ring
  rw [hcongr]
  have hu : ∀ x ∈ Set.uIcc (n : ℝ) (n + 1),
      HasDerivAt (fun x : ℝ => (x : ℂ) - n - 1 / 2) 1 x := by
    intro x _
    exact ((hasDerivAt_id x).ofReal_comp.sub_const _).sub_const _
  have hv : ∀ x ∈ Set.uIcc (n : ℝ) (n + 1),
      HasDerivAt (ph t 0) (((t / x : ℝ) : ℂ) * I * ph t 0 x) x := by
    intro x hx
    have : 0 < x := lt_of_lt_of_le (lt_min hn0 (by linarith)) hx.1
    exact hasDerivAt_ph0 t x this
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv intervalIntegrable_const
    ((contOn_fd t _ _ hn0 (by linarith)).intervalIntegrable)]
  simp only [one_mul, phaseInt]
  push_cast; ring

theorem em_identity (t : ℝ) (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ioc a b, ph t 0 n =
      phaseInt t 0 a b
        + (∫ x in (a : ℝ)..b, (saw x : ℂ) * (((t / x : ℝ) : ℂ) * I * ph t 0 x))
        + (ph t 0 b - ph t 0 a) / 2 := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  induction b, hab using Nat.le_induction with
  | base => simp [phaseInt]
  | succ b hab ih =>
    have hb0 : (0 : ℝ) < b := by have : (a : ℝ) ≤ b := by exact_mod_cast hab
                                 linarith
    have hb1 : (1:ℕ) ≤ b := le_trans ha hab
    have e1 := intervalIntegral.integral_add_adjacent_intervals
        ((contOn_ph t 0 _ _ ha0 hb0).intervalIntegrable (μ := volume))
        ((contOn_ph t 0 (b : ℝ) ((b : ℝ) + 1) hb0 (by linarith)).intervalIntegrable (μ := volume))
    have e2 := intervalIntegral.integral_add_adjacent_intervals (ii_saw_fd t _ _ ha0 hb0)
        (ii_saw_fd t (b : ℝ) ((b : ℝ) + 1) hb0 (by linarith))
    have e3 := em_unit t b hb1
    rw [Finset.sum_Ioc_succ_top hab, ih]
    simp only [Nat.cast_add, Nat.cast_one]
    unfold phaseInt at *
    rw [← e1, ← e2, e3]
    ring

end GuthMaynard.BProc.PartB
end

section
open Complex Real MeasureTheory intervalIntegral Finset
namespace GuthMaynard.BProc
/-! ### Part B: Euler–Maclaurin and the sawtooth expansion -/
alias em_identity := GuthMaynard.BProc.PartB.em_identity

end GuthMaynard.BProc
end

section
open Complex Real MeasureTheory intervalIntegral Finset
namespace GuthMaynard.BProc.PartB
open GuthMaynard.BProc
/-! ### Symmetric sums over `1 ≤ |μ| ≤ K` -/
lemma sum_S {M : Type*} [AddCommMonoid M] (f : ℤ → M) (K : ℕ) :
    ∑ μ ∈ (Icc (-(K : ℤ)) K).erase 0, f μ = ∑ n ∈ range K, (f ((n : ℤ) + 1) + f (-((n : ℤ) + 1))) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have : (Icc (-((K + 1 : ℕ) : ℤ)) ((K + 1 : ℕ) : ℤ)).erase 0 =
        insert ((K : ℤ) + 1) (insert (-((K : ℤ) + 1)) ((Icc (-(K : ℤ)) K).erase 0)) := by
      ext μ; simp only [mem_erase, mem_Icc, mem_insert]; push_cast; omega
    rw [this, sum_insert (by simp only [mem_erase, mem_Icc, mem_insert]; omega),
      sum_insert (by simp only [mem_erase, mem_Icc]; omega), ih, sum_range_succ]
    abel

lemma sum_S_neg {M : Type*} [AddCommMonoid M] (f : ℤ → M) (K : ℕ) :
    ∑ μ ∈ (Icc (-(K : ℤ)) K).erase 0, f (-μ) = ∑ μ ∈ (Icc (-(K : ℤ)) K).erase 0, f μ := by
  rw [sum_S (fun μ => f (-μ)), sum_S]
  refine sum_congr rfl (fun n _ => ?_)
  simp only [neg_neg]; exact add_comm _ _

lemma sum_S_odd {G : Type*} [AddCommGroup G] (f : ℤ → G) (hf : ∀ μ, f (-μ) = -f μ) (K : ℕ) :
    ∑ μ ∈ (Icc (-(K : ℤ)) K).erase 0, f μ = 0 := by
  rw [sum_S]
  refine sum_eq_zero (fun n _ => ?_)
  rw [hf]; simp

/-! ### The sawtooth expansion -/
lemma E_nat (μ : ℤ) (n : ℕ) : Complex.exp (2 * π * (μ : ℂ) * (((n : ℕ) : ℝ) : ℂ) * I) = 1 := by
  rw [← Complex.exp_int_mul_two_pi_mul_I (μ * n)]; congr 1; push_cast; ring

lemma hasDerivAt_E (μ : ℤ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.exp (2 * π * (μ : ℂ) * (x : ℂ) * I))
      (Complex.exp (2 * π * (μ : ℂ) * (x : ℂ) * I) * (2 * π * (μ : ℂ) * I)) x := by
  have h : HasDerivAt (fun y : ℝ => 2 * π * (μ : ℂ) * (y : ℂ) * I)
      (2 * π * (μ : ℂ) * ((1 : ℝ) : ℂ) * I) x :=
    ((hasDerivAt_id' x).ofReal_comp.const_mul (2 * π * (μ : ℂ))).mul_const I
  convert h.cexp using 1
  push_cast; ring

lemma contE (μ : ℤ) : Continuous (fun x : ℝ => Complex.exp (2 * π * (μ : ℂ) * (x : ℂ) * I)) := by
  fun_prop

lemma ibp_mu (t : ℝ) (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) (μ : ℤ) :
    ∫ x in (a : ℝ)..b, Complex.exp (2 * π * (μ : ℂ) * (x : ℂ) * I) *
        (((t / x : ℝ) : ℂ) * I * ph t 0 x)
      = ph t 0 b - ph t 0 a - 2 * π * (μ : ℂ) * I * phaseInt t (2 * π * ((-μ : ℤ) : ℝ)) a b := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hb0 : (0 : ℝ) < b := by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  have hv : ∀ x ∈ Set.uIcc (a : ℝ) b,
      HasDerivAt (ph t 0) (((t / x : ℝ) : ℂ) * I * ph t 0 x) x := by
    intro x hx
    have : 0 < x := lt_of_lt_of_le (lt_min ha0 hb0) hx.1
    exact hasDerivAt_ph0 t x this
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun x _ => hasDerivAt_E μ x) hv
    (((contE μ).mul continuous_const).intervalIntegrable _ _)
    ((contOn_fd t _ _ ha0 hb0).intervalIntegrable)]
  rw [E_nat, E_nat]
  have : ∀ x : ℝ, Complex.exp (2 * π * (μ : ℂ) * (x : ℂ) * I) * (2 * π * (μ : ℂ) * I) * ph t 0 x
      = (2 * π * (μ : ℂ) * I) * ph t (2 * π * ((-μ : ℤ) : ℝ)) x := by
    intro x
    unfold ph
    rw [mul_comm (Complex.exp _), mul_assoc, ← Complex.exp_add]
    congr 2; push_cast; ring
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul, phaseInt]
  ring

theorem saw_expand (t : ℝ) (a b K : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ x in (a : ℝ)..b, (saw x : ℂ) * (((t / x : ℝ) : ℂ) * I * ph t 0 x)) =
      ∑ ν ∈ (Finset.Icc (-(K : ℤ)) K).erase 0, phaseInt t (2 * π * ν) a b
        + ∫ x in (a : ℝ)..b, sawTail K x * (((t / x : ℝ) : ℂ) * I * ph t 0 x) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hb0 : (0 : ℝ) < b := by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  have hsplit : ∀ x : ℝ, sawTail K x * (((t / x : ℝ) : ℂ) * I * ph t 0 x) =
      (saw x : ℂ) * (((t / x : ℝ) : ℂ) * I * ph t 0 x) +
        ∑ μ ∈ (Icc (-(K : ℤ)) K).erase 0, (1 / (2 * π * (μ : ℂ) * I)) *
          (Complex.exp (2 * π * (μ : ℂ) * (x : ℂ) * I) * (((t / x : ℝ) : ℂ) * I * ph t 0 x)) := by
    intro x
    unfold sawTail
    rw [add_mul, Finset.sum_mul]
    congr 1
    refine sum_congr rfl (fun μ _ => ?_)
    ring
  have hcont : ∀ μ : ℤ, ContinuousOn (fun x : ℝ => (1 / (2 * π * (μ : ℂ) * I)) *
      (Complex.exp (2 * π * (μ : ℂ) * (x : ℂ) * I) * (((t / x : ℝ) : ℂ) * I * ph t 0 x)))
      (Set.uIcc (a : ℝ) b) := fun μ =>
    continuousOn_const.mul ((contE μ).continuousOn.mul (contOn_fd t _ _ ha0 hb0))
  have hT : ∫ x in (a : ℝ)..b, sawTail K x * (((t / x : ℝ) : ℂ) * I * ph t 0 x) =
      (∫ x in (a : ℝ)..b, (saw x : ℂ) * (((t / x : ℝ) : ℂ) * I * ph t 0 x)) +
        ∑ μ ∈ (Icc (-(K : ℤ)) K).erase 0, (1 / (2 * π * (μ : ℂ) * I)) *
          ∫ x in (a : ℝ)..b, Complex.exp (2 * π * (μ : ℂ) * (x : ℂ) * I) *
            (((t / x : ℝ) : ℂ) * I * ph t 0 x) := by
    simp_rw [hsplit]
    rw [intervalIntegral.integral_add (ii_saw_fd t _ _ ha0 hb0)
      ((continuousOn_finsetSum _ (fun μ _ => hcont μ)).intervalIntegrable),
      intervalIntegral.integral_finsetSum (fun μ _ => (hcont μ).intervalIntegrable)]
    congr 1
    refine sum_congr rfl (fun μ _ => ?_)
    rw [intervalIntegral.integral_const_mul]
  have hI : ∀ μ ∈ (Icc (-(K : ℤ)) K).erase 0, (1 / (2 * π * (μ : ℂ) * I)) *
      (∫ x in (a : ℝ)..b, Complex.exp (2 * π * (μ : ℂ) * (x : ℂ) * I) *
            (((t / x : ℝ) : ℂ) * I * ph t 0 x)) =
      (ph t 0 b - ph t 0 a) / (2 * π * (μ : ℂ) * I) - phaseInt t (2 * π * ((-μ : ℤ) : ℝ)) a b := by
    intro μ hμ
    have hμ0 : (μ : ℂ) ≠ 0 := by exact_mod_cast (mem_erase.1 hμ).1
    have hd : (2 * π * (μ : ℂ) * I) ≠ 0 := by
      have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [hμ0, this, Complex.I_ne_zero]
    rw [ibp_mu t a b ha hab μ]
    field_simp
  have hodd := sum_S_odd (fun μ : ℤ => (ph t 0 b - ph t 0 a) / (2 * π * (μ : ℂ) * I))
    (fun μ => by push_cast; ring) K
  have hneg := sum_S_neg (fun ν : ℤ => phaseInt t (2 * π * (ν : ℝ)) a b) K
  beta_reduce at hodd hneg
  rw [hT, sum_congr rfl hI, sum_sub_distrib, hodd, hneg]
  ring

end GuthMaynard.BProc.PartB
end

section
open Complex Real MeasureTheory intervalIntegral Finset
namespace GuthMaynard.BProc
alias saw_expand := GuthMaynard.BProc.PartB.saw_expand

end GuthMaynard.BProc
end

section
open Complex Real MeasureTheory intervalIntegral Finset
namespace GuthMaynard.BProc.PartB
open GuthMaynard.BProc
/-! ### The `L²` norm of the tail on `[0, 1]` -/
/-- `e(μx)`. -/
noncomputable def E (μ : ℤ) (x : ℝ) : ℂ := Complex.exp (2 * π * (μ : ℂ) * (x : ℂ) * I)

/-- `2πiμ`. -/
noncomputable def dd (μ : ℤ) : ℂ := 2 * π * (μ : ℂ) * I

/-- The Fourier polynomial part of `sawTail`. -/
noncomputable def P (K : ℕ) (x : ℝ) : ℂ := ∑ μ ∈ (Icc (-(K : ℤ)) K).erase 0, E μ x / dd μ

lemma sawTail_eq (K : ℕ) (x : ℝ) : sawTail K x = (saw x : ℂ) + P K x := rfl

lemma dd_ne (μ : ℤ) (hμ : μ ≠ 0) : dd μ ≠ 0 := by
  have hμ0 : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ
  have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp [dd, hμ0, this, Complex.I_ne_zero]

lemma contE' (μ : ℤ) : Continuous (E μ) := by unfold E; fun_prop

lemma contP (K : ℕ) : Continuous (P K) := by
  unfold P; exact continuous_finsetSum _ (fun μ _ => (contE' μ).div_const _)

lemma E_add (μ ν : ℤ) (x : ℝ) : E μ x * E ν x = E (μ + ν) x := by
  unfold E; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma intE (j : ℤ) : ∫ x in (0 : ℝ)..1, E j x = if j = 0 then 1 else 0 := by
  split_ifs with hj
  · subst hj; simp [E]
  · have hc : (2 * π * (j : ℂ) * I) ≠ 0 := dd_ne j hj
    have : ∀ x : ℝ, E j x = Complex.exp ((2 * π * (j : ℂ) * I) * (x : ℂ)) := by
      intro x; unfold E; ring_nf
    simp_rw [this]
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp ((2 * π * (j : ℂ) * I) * ((1 : ℝ) : ℂ)) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I j]; congr 1; push_cast; ring
    rw [h1]; simp

lemma intSawE (μ : ℤ) (hμ : μ ≠ 0) :
    ∫ x in (0 : ℝ)..1, (saw x : ℂ) * E μ x = 1 / dd μ := by
  have hd := dd_ne μ hμ
  have hcongr : ∫ x in (0 : ℝ)..1, (saw x : ℂ) * E μ x =
      ∫ x in (0 : ℝ)..1, ((x : ℂ) - 1 / 2) * E μ x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with x hx hmem
    rw [Set.uIoc_of_le (by norm_num)] at hmem
    have := saw_eq_on 0 x (by exact_mod_cast hmem.1.le)
      (by have := lt_of_le_of_ne hmem.2 hx; push_cast; linarith)
    rw [this]; push_cast; ring
  rw [hcongr]
  have hu : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun x : ℝ => (x : ℂ) - 1 / 2) 1 x := by
    intro x _
    exact (hasDerivAt_id x).ofReal_comp.sub_const _
  have hv : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun x => E μ x / dd μ) (E μ x) x := by
    intro x _
    have h2 : HasDerivAt (fun x => E μ x / dd μ) (E μ x * dd μ / dd μ) x :=
      (hasDerivAt_E μ x).div_const (dd μ)
    rwa [mul_div_cancel_right₀ _ hd] at h2
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv intervalIntegrable_const
    ((contE' μ).intervalIntegrable _ _)]
  simp only [one_mul]
  rw [intervalIntegral.integral_div, intE, if_neg hμ]
  have h0 : E μ 0 = 1 := by simp [E]
  have h1 : E μ 1 = 1 := by
    have := E_nat μ 1; simpa [E] using this
  rw [h0, h1]; push_cast; field_simp; ring

lemma intSaw2 : ∫ x in (0 : ℝ)..1, (saw x : ℂ) * (saw x : ℂ) = 1 / 12 := by
  have hcongr : ∫ x in (0 : ℝ)..1, (saw x : ℂ) * (saw x : ℂ) =
      ∫ x in (0 : ℝ)..1, (((x - 1 / 2) ^ 2 : ℝ) : ℂ) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with x hx hmem
    rw [Set.uIoc_of_le (by norm_num)] at hmem
    have := saw_eq_on 0 x (by exact_mod_cast hmem.1.le)
      (by have := lt_of_le_of_ne hmem.2 hx; push_cast; linarith)
    rw [this]; push_cast; ring
  rw [hcongr, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_comp_sub_right (fun x => x ^ 2) (1 / 2), integral_pow]
  norm_num

lemma conj_E (μ : ℤ) (x : ℝ) : (starRingEnd ℂ) (E μ x) = E (-μ) x := by
  unfold E
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, map_intCast]
  push_cast; ring

lemma conj_dd (μ : ℤ) : (starRingEnd ℂ) (dd μ) = dd (-μ) := by
  unfold dd
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, map_intCast]
  push_cast; ring

lemma conj_P (K : ℕ) (x : ℝ) : (starRingEnd ℂ) (P K x) = P K x := by
  unfold P
  rw [map_sum]
  simp_rw [map_div₀, conj_E, conj_dd]
  exact sum_S_neg (fun μ => E μ x / dd μ) K

lemma normSq_R (K : ℕ) (x : ℝ) : ((‖sawTail K x‖ ^ 2 : ℝ) : ℂ) = sawTail K x * sawTail K x := by
  have h := Complex.mul_conj' (sawTail K x)
  have hc : (starRingEnd ℂ) (sawTail K x) = sawTail K x := by
    rw [sawTail_eq, map_add, conj_P, Complex.conj_ofReal]
  rw [hc] at h
  rw [h]; push_cast; ring

lemma ii_sawsaw : IntervalIntegrable (fun x => (saw x : ℂ) * (saw x : ℂ)) volume 0 1 := by
  refine ii_bdd (f := fun x => (saw x : ℂ) * (saw x : ℂ))
    (saw_meas.mul saw_meas).aestronglyMeasurable (M := 1 * 1) (fun x => ?_) 0 1
  rw [norm_mul]
  exact mul_le_mul (norm_saw_le x) (norm_saw_le x) (norm_nonneg _) zero_le_one

lemma intR2 (K : ℕ) : ∫ x in (0 : ℝ)..1, sawTail K x * sawTail K x =
    1 / 12 + ∑ μ ∈ (Icc (-(K : ℤ)) K).erase 0, 1 / (dd μ) ^ 2 := by
  have hexp : ∀ x, sawTail K x * sawTail K x = (saw x : ℂ) * (saw x : ℂ) +
      (2 * ((saw x : ℂ) * P K x) + P K x * P K x) := by
    intro x; rw [sawTail_eq]; ring
  simp_rw [hexp]
  have ii2 : IntervalIntegrable (fun x => 2 * ((saw x : ℂ) * P K x)) volume 0 1 :=
    ((ii_saw 0 1).mul_continuousOn (contP K).continuousOn).const_mul 2
  have ii3 : IntervalIntegrable (fun x => P K x * P K x) volume 0 1 :=
    ((contP K).mul (contP K)).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add ii_sawsaw (ii2.add ii3), intervalIntegral.integral_add ii2 ii3,
    intervalIntegral.integral_const_mul, intSaw2]
  have hSP : ∫ x in (0 : ℝ)..1, (saw x : ℂ) * P K x =
      ∑ μ ∈ (Icc (-(K : ℤ)) K).erase 0, 1 / (dd μ) ^ 2 := by
    have : ∀ x, (saw x : ℂ) * P K x =
        ∑ μ ∈ (Icc (-(K : ℤ)) K).erase 0, (1 / dd μ) * ((saw x : ℂ) * E μ x) := by
      intro x; unfold P; rw [mul_sum]; exact sum_congr rfl (fun μ _ => by ring)
    simp_rw [this]
    rw [intervalIntegral.integral_finsetSum
      (fun μ _ => ((ii_saw 0 1).mul_continuousOn (contE' μ).continuousOn).const_mul _)]
    refine sum_congr rfl (fun μ hμ => ?_)
    rw [intervalIntegral.integral_const_mul, intSawE μ (mem_erase.1 hμ).1]; ring
  have hPP : ∫ x in (0 : ℝ)..1, P K x * P K x =
      -∑ μ ∈ (Icc (-(K : ℤ)) K).erase 0, 1 / (dd μ) ^ 2 := by
    have : ∀ x, P K x * P K x = ∑ μ ∈ (Icc (-(K : ℤ)) K).erase 0,
        ∑ ν ∈ (Icc (-(K : ℤ)) K).erase 0, (1 / (dd μ * dd ν)) * E (μ + ν) x := by
      intro x; unfold P; rw [sum_mul_sum]
      refine sum_congr rfl (fun μ _ => sum_congr rfl (fun ν _ => ?_))
      rw [← E_add]; ring
    simp_rw [this]
    rw [intervalIntegral.integral_finsetSum
      (f := fun μ x => ∑ ν ∈ (Icc (-(K : ℤ)) K).erase 0, (1 / (dd μ * dd ν)) * E (μ + ν) x)
      (fun μ _ => (continuous_finsetSum _ (fun ν _ => continuous_const.mul (contE' _))).intervalIntegrable 0 1)]
    rw [← sum_neg_distrib]
    refine sum_congr rfl (fun μ hμ => ?_)
    rw [intervalIntegral.integral_finsetSum (f := fun ν x => (1 / (dd μ * dd ν)) * E (μ + ν) x)
      (fun ν _ => (continuous_const.mul (contE' _)).intervalIntegrable 0 1)]
    simp_rw [intervalIntegral.integral_const_mul, intE]
    rw [sum_eq_single (-μ)]
    · rw [if_pos (by ring)]
      have : dd (-μ) = -dd μ := by unfold dd; push_cast; ring
      rw [this]; ring
    · intro ν _ hne
      rw [if_neg (by omega)]; simp
    · intro h; exfalso; apply h
      simp only [mem_erase, mem_Icc] at hμ ⊢; omega
  rw [hSP, hPP]; ring

lemma sum_inv_dd2 (K : ℕ) : ∑ μ ∈ (Icc (-(K : ℤ)) K).erase 0, 1 / (dd μ) ^ 2 =
    ((-(1 / (2 * π ^ 2)) * ∑ n ∈ range K, 1 / ((n : ℝ) + 1) ^ 2 : ℝ) : ℂ) := by
  rw [sum_S, Complex.ofReal_mul, Complex.ofReal_sum, mul_sum]
  refine sum_congr rfl (fun n _ => ?_)
  have key : ∀ m : ℂ, (2 * π * m * I) ^ 2 = -(4 * π ^ 2 * m ^ 2) := by
    intro m; ring_nf; rw [Complex.I_sq]; ring
  have hm : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold dd
  push_cast
  rw [key, key]
  field_simp
  ring

lemma zeta_tail (K : ℕ) : π ^ 2 / 6 ≤ ∑ n ∈ range K, 1 / ((n : ℝ) + 1) ^ 2 + 2 / ((K : ℝ) + 1) := by
  apply le_of_tendsto' hasSum_zeta_two.tendsto_sum_nat
  intro m
  have h1 : ∑ i ∈ range m, 1 / (i : ℝ) ^ 2 ≤ ∑ i ∈ range (m + (K + 1)), 1 / (i : ℝ) ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega)) (fun _ _ _ => by positivity)
  rw [← sum_range_add_sum_Ico _ (show K + 1 ≤ m + (K + 1) by omega), sum_range_succ'] at h1
  have h2 : ∑ i ∈ Ico (K + 1) (m + (K + 1)), 1 / (i : ℝ) ^ 2 ≤ 2 / ((K : ℝ) + 1) := by
    have := sum_Ioo_inv_sq_le (α := ℝ) K (m + (K + 1))
    have e : Ioo K (m + (K + 1)) = Ico (K + 1) (m + (K + 1)) := by
      ext i; simp only [mem_Ioo, mem_Ico]; omega
    rw [e] at this
    simpa [one_div] using this
  push_cast at h1
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    div_zero, add_zero] at h1
  linarith

lemma meas_sawTail (K : ℕ) : Measurable (sawTail K) := by unfold sawTail saw; fun_prop

lemma norm_E (μ : ℤ) (x : ℝ) : ‖E μ x‖ = 1 := by
  have : E μ x = Complex.exp (((2 * π * μ * x : ℝ) : ℂ) * I) := by unfold E; push_cast; ring_nf
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma norm_dd_ge (μ : ℤ) (hμ : μ ≠ 0) : 1 ≤ ‖dd μ‖ := by
  unfold dd
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_intCast, Complex.norm_real,
    Complex.norm_ofNat, Real.norm_of_nonneg Real.pi_pos.le]
  have : (1 : ℝ) ≤ |(μ : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hμ
  nlinarith [Real.pi_gt_three]

lemma norm_sawTail_le (K : ℕ) (x : ℝ) :
    ‖sawTail K x‖ ≤ 1 + ((Icc (-(K : ℤ)) K).erase 0).card := by
  rw [sawTail_eq]
  refine (norm_add_le _ _).trans (add_le_add (norm_saw_le x) ?_)
  unfold P
  refine (norm_sum_le _ _).trans ?_
  have : ∀ μ ∈ (Icc (-(K : ℤ)) K).erase 0, ‖E μ x / dd μ‖ ≤ 1 := by
    intro μ hμ
    rw [norm_div, norm_E, div_le_one (by linarith [norm_dd_ge μ (mem_erase.1 hμ).1])]
    exact norm_dd_ge μ (mem_erase.1 hμ).1
  refine (sum_le_sum this).trans ?_
  simp

lemma iiN (K : ℕ) (a b : ℝ) : IntervalIntegrable (fun x => ‖sawTail K x‖) volume a b :=
  ii_bdd (meas_sawTail K).norm.aestronglyMeasurable (fun x => by
    rw [norm_norm]; exact norm_sawTail_le K x) a b

lemma iiN2 (K : ℕ) (a b : ℝ) : IntervalIntegrable (fun x => ‖sawTail K x‖ ^ 2) volume a b := by
  refine ii_bdd ((meas_sawTail K).norm.pow_const 2).aestronglyMeasurable
    (M := (1 + ((Icc (-(K : ℤ)) K).erase 0).card) ^ 2) (fun x => ?_) a b
  rw [Real.norm_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_sawTail_le K x) 2

lemma int_normsq (K : ℕ) (hK : 1 ≤ K) : ∫ x in (0 : ℝ)..1, ‖sawTail K x‖ ^ 2 ≤ 1 / K := by
  have h : ((∫ x in (0 : ℝ)..1, ‖sawTail K x‖ ^ 2 : ℝ) : ℂ) =
      ((1 / 12 + -(1 / (2 * π ^ 2)) * ∑ n ∈ range K, 1 / ((n : ℝ) + 1) ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    simp_rw [normSq_R]
    rw [intR2, sum_inv_dd2]; push_cast; ring
  have h' := Complex.ofReal_injective h
  rw [h']
  have hz := zeta_tail K
  have hπ : 0 < π ^ 2 := by positivity
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have e1 : (1 / (2 * π ^ 2)) * (π ^ 2 / 6) = 1 / 12 := by field_simp; ring
  have e2 : (1 / (2 * π ^ 2)) * (2 / ((K : ℝ) + 1)) = 1 / (π ^ 2 * ((K : ℝ) + 1)) := by
    field_simp
  have m := mul_le_mul_of_nonneg_left hz (show 0 ≤ 1 / (2 * π ^ 2) by positivity)
  rw [mul_add, e1, e2] at m
  have h3 : 1 / (π ^ 2 * ((K : ℝ) + 1)) ≤ 1 / (K : ℝ) :=
    one_div_le_one_div_of_le hK0 (by
      have : (1 : ℝ) ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
      nlinarith [mul_le_mul_of_nonneg_right this (show (0:ℝ) ≤ K + 1 by positivity)])
  linarith

lemma int_norm (K : ℕ) (hK : 1 ≤ K) : ∫ x in (0 : ℝ)..1, ‖sawTail K x‖ ≤ 1 / Real.sqrt K := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  set r := Real.sqrt K with hr_def
  have hr : 0 < r := Real.sqrt_pos.2 hK0
  have hr2 : r ^ 2 = K := Real.sq_sqrt hK0.le
  have hpt : ∀ x, ‖sawTail K x‖ ≤ (r / 2) * ‖sawTail K x‖ ^ 2 + 1 / (2 * r) := by
    intro x
    set y := ‖sawTail K x‖
    rw [← sub_nonneg]
    have : (r / 2) * y ^ 2 + 1 / (2 * r) - y = (r * y - 1) ^ 2 / (2 * r) := by
      field_simp; ring
    rw [this]; positivity
  calc ∫ x in (0 : ℝ)..1, ‖sawTail K x‖
      ≤ ∫ x in (0 : ℝ)..1, ((r / 2) * ‖sawTail K x‖ ^ 2 + 1 / (2 * r)) :=
        intervalIntegral.integral_mono_on (by norm_num) (iiN K 0 1)
          (((iiN2 K 0 1).const_mul _).add intervalIntegrable_const) (fun x _ => hpt x)
    _ = (r / 2) * (∫ x in (0 : ℝ)..1, ‖sawTail K x‖ ^ 2) + 1 / (2 * r) := by
        rw [intervalIntegral.integral_add ((iiN2 K 0 1).const_mul _) intervalIntegrable_const,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
        simp
    _ ≤ (r / 2) * (1 / K) + 1 / (2 * r) := by gcongr; exact int_normsq K hK
    _ = 1 / r := by rw [← hr2]; field_simp; ring

lemma saw_periodic (x : ℝ) : saw (x + 1) = saw x := by
  unfold saw; rw [Int.floor_add_one]; push_cast; ring

lemma E_periodic (μ : ℤ) (x : ℝ) : E μ (x + 1) = E μ x := by
  unfold E
  have : 2 * π * (μ : ℂ) * (((x + 1 : ℝ)) : ℂ) * I = 2 * π * (μ : ℂ) * (x : ℂ) * I + μ * (2 * π * I) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

lemma sawTail_periodic (K : ℕ) : Function.Periodic (fun x => ‖sawTail K x‖) 1 := by
  intro x
  simp only [sawTail_eq, P, saw_periodic, E_periodic]

lemma int_ab (K : ℕ) (a b : ℕ) (hab : a ≤ b) :
    ∫ x in (a : ℝ)..b, ‖sawTail K x‖ = ((b : ℝ) - a) * ∫ x in (0 : ℝ)..1, ‖sawTail K x‖ := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have := (sawTail_periodic K).intervalIntegral_add_eq (b : ℝ) 0
    rw [zero_add] at this
    push_cast
    rw [← intervalIntegral.integral_add_adjacent_intervals (iiN K a b) (iiN K b (b + 1)), ih, this]
    ring

theorem tail_term_le (t : ℝ) (ht : 0 < t) (a b K : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) (hK : 1 ≤ K) :
    ‖∫ x in (a : ℝ)..b, sawTail K x * (((t / x : ℝ) : ℂ) * I * ph t 0 x)‖ ≤
      t / a * (b - a) / Real.sqrt K := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hle : ‖∫ x in (a : ℝ)..b, sawTail K x * (((t / x : ℝ) : ℂ) * I * ph t 0 x)‖ ≤
      ∫ x in (a : ℝ)..b, ‖sawTail K x‖ * (t / a) := by
    refine intervalIntegral.norm_integral_le_of_norm_le habR (ae_of_all _ (fun x hx => ?_))
      ((iiN K a b).mul_const _)
    have hx0 : 0 < x := lt_trans ha0 hx.1
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, norm_ph, Complex.norm_real,
      Real.norm_of_nonneg (by positivity), mul_one, mul_one]
    gcongr
    exact hx.1.le
  refine hle.trans ?_
  rw [intervalIntegral.integral_mul_const, int_ab K a b hab]
  have := int_norm K hK
  have hba : (0 : ℝ) ≤ b - a := by linarith
  calc ((b : ℝ) - a) * (∫ x in (0 : ℝ)..1, ‖sawTail K x‖) * (t / a)
      ≤ ((b : ℝ) - a) * (1 / Real.sqrt K) * (t / a) := by gcongr
    _ = t / a * (b - a) / Real.sqrt K := by ring

end GuthMaynard.BProc.PartB
end

section
open Complex Real MeasureTheory intervalIntegral Finset
namespace GuthMaynard.BProc
alias tail_term_le := GuthMaynard.BProc.PartB.tail_term_le

/-! ### Part C: the non-stationary and the stationary frequencies -/
/-- The window of stationary frequencies, `t/(2πb) ≤ ν ≤ t/(2πa)`. -/
def InWindow (t : ℝ) (a b : ℕ) (ν : ℤ) : Prop :=
  t / (2 * π * b) ≤ ν ∧ (ν : ℝ) ≤ t / (2 * π * a)

noncomputable instance (t : ℝ) (a b : ℕ) : DecidablePred (InWindow t a b) :=
  fun _ => Classical.dec _

end GuthMaynard.BProc
end

section
open Complex Real MeasureTheory intervalIntegral Finset
namespace GuthMaynard.BProc.PartC
open GuthMaynard.BProc

lemma hasDerivAt_ph (t c x : ℝ) (hx : 0 < x) :
    HasDerivAt (ph t c) (((t / x - c : ℝ) : ℂ) * I * ph t c x) x := by
  have h1 : HasDerivAt (fun y => t * Real.log y - c * y) (t * x⁻¹ - c) x := by
    have := ((Real.hasDerivAt_log hx.ne').const_mul t).sub ((hasDerivAt_id x).const_mul c)
    exact this.congr_deriv (by simp)
  have h2 := (h1.ofReal_comp.mul_const I).cexp
  have hph : ph t c = fun x => Complex.exp (((t * Real.log x - c * x : ℝ) : ℂ) * I) := rfl
  rw [hph]
  convert h2 using 1
  push_cast
  ring

lemma ph_intervalIntegrable (t c u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    IntervalIntegrable (ph t c) volume u v := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_of_forall_continuousAt
  intro x hx
  have : 0 < x := by
    rcases Set.mem_uIcc.mp hx with h | h <;> linarith [h.1]
  exact (hasDerivAt_ph t c x this).continuousAt

lemma phaseInt_split (t c u w v : ℝ) (hu : 0 < u) (hw : 0 < w) (hv : 0 < v) :
    phaseInt t c u v = phaseInt t c u w + phaseInt t c w v := by
  unfold phaseInt
  rw [integral_add_adjacent_intervals (ph_intervalIntegrable t c u w hu hw)
    (ph_intervalIntegrable t c w v hw hv)]

/-! ### rescale -/
lemma ph_rescale (t : ℝ) (ν : ℕ) (hν : 1 ≤ ν) (x : ℝ) (hx : x ≠ 0) :
    ph t (2 * π * ν) x = (ν : ℂ) ^ (-(t : ℂ) * I) * ph t (2 * π) (ν * x) := by
  have hν0 : (ν : ℝ) ≠ 0 := by positivity
  have hνc : (ν : ℂ) ≠ 0 := by exact_mod_cast hν0
  unfold ph
  rw [Complex.cpow_def_of_ne_zero hνc, ← Complex.exp_add]
  congr 1
  have hlog : Complex.log (ν : ℂ) = ((Real.log ν : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by positivity)]
    simp
  rw [hlog, Real.log_mul hν0 hx]
  push_cast
  ring

theorem rescale (t a b : ℝ) (ν : ℕ) (hν : 1 ≤ ν) :
    phaseInt t (2 * π * ν) a b =
      (1 / (ν : ℂ)) * (ν : ℂ) ^ (-(t : ℂ) * I) * phaseInt t (2 * π) (ν * a) (ν * b) := by
  have hν0 : (ν : ℝ) ≠ 0 := by positivity
  unfold phaseInt
  have h1 : (∫ x in a..b, ph t (2 * π * ν) x) =
      ∫ x in a..b, (ν : ℂ) ^ (-(t : ℂ) * I) * ph t (2 * π) (ν * x) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume 0] with x hx _
    exact ph_rescale t ν hν x hx
  rw [h1, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun y => ph t (2 * π) y) hν0, Complex.real_smul]
  push_cast
  ring

/-! ### window -/
theorem window_sum_eq (t : ℝ) (ht : 0 < t) (a b K : ℕ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hK : t / (2 * π * a) ≤ K) (f : ℝ → ℂ) :
    ∑ ν ∈ (Finset.Icc (-(K : ℤ)) K).filter (fun ν => InWindow t a b ν), f ν =
      ∑ ν ∈ Finset.Icc ⌈t / (2 * π * b)⌉₊ ⌊t / (2 * π * a)⌋₊, f ν := by
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast ha.trans hab
  have hα : 0 < t / (2 * π * b) := by positivity
  have hβ : 0 ≤ t / (2 * π * a) := by positivity
  have hset : (Finset.Icc (-(K : ℤ)) K).filter (fun ν => InWindow t a b ν) =
      (Finset.Icc ⌈t / (2 * π * b)⌉₊ ⌊t / (2 * π * a)⌋₊).image (fun n : ℕ => (n : ℤ)) := by
    ext ν
    rw [Finset.mem_filter]
    simp only [Finset.mem_Icc, Finset.mem_image]
    unfold InWindow
    constructor
    · rintro ⟨⟨_, _⟩, h3, h4⟩
      have h0 : 0 ≤ ν := by
        have : (0 : ℝ) < ν := lt_of_lt_of_le hα h3
        exact_mod_cast this.le
      lift ν to ℕ using h0
      refine ⟨ν, ⟨Nat.ceil_le.mpr (by exact_mod_cast h3), Nat.le_floor (by exact_mod_cast h4)⟩,
        rfl⟩
    · rintro ⟨n, ⟨h1, h2⟩, rfl⟩
      have h3 : t / (2 * π * b) ≤ n := Nat.ceil_le.mp h1
      have h4 : (n : ℝ) ≤ t / (2 * π * a) := (Nat.le_floor_iff hβ).mp h2
      have h5 : n ≤ K := by exact_mod_cast h4.trans hK
      refine ⟨⟨by omega, by exact_mod_cast h5⟩, by exact_mod_cast h3, by exact_mod_cast h4⟩
  rw [hset, Finset.sum_image (fun x _ y _ h => by exact_mod_cast h)]
  simp

/-! ### harmonic-type sums -/
lemma sum_harm {ι : Type*} (S : Finset ι) (g : ι → ℕ) (hinj : Set.InjOn g S) (N : ℕ)
    (hg : ∀ x ∈ S, g x ≤ N) (f : ι → ℝ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ x ∈ S, f x ≤ if g x = 0 then A else B / g x) :
    ∑ x ∈ S, f x ≤ A + B * (1 + Real.log N) := by
  set F : ℕ → ℝ := fun j => if j = 0 then A else B / j with hF
  have hFnn : ∀ j, 0 ≤ F j := by
    intro j; simp only [hF]; split_ifs <;> positivity
  calc ∑ x ∈ S, f x ≤ ∑ x ∈ S, F (g x) := sum_le_sum hf
    _ = ∑ j ∈ S.image g, F j := (sum_image (fun x hx y hy h => hinj hx hy h)).symm
    _ ≤ ∑ j ∈ range (N + 1), F j := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro j hj
          obtain ⟨x, hx, rfl⟩ := mem_image.mp hj
          exact mem_range.mpr (Nat.lt_succ_of_le (hg x hx))
        · intro j _ _; exact hFnn j
    _ = A + B * (harmonic N : ℝ) := by
        rw [sum_range_succ', add_comm]
        congr 1
        simp only [hF, harmonic, Nat.add_one_ne_zero, if_false, Rat.cast_sum, Rat.cast_inv,
          Rat.cast_natCast, mul_sum, div_eq_mul_inv]
    _ ≤ A + B * (1 + Real.log N) := by
        gcongr
        exact harmonic_le_one_add_log N

lemma log_nat_le (n : ℕ) (y : ℝ) (hy : 1 ≤ y) (h : (n : ℝ) ≤ y) : Real.log n ≤ Real.log y := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [Real.log_nonneg hy]
  · exact Real.log_le_log (by exact_mod_cast hn) h

/-! ### non-stationary frequencies -/
lemma fd_const (j : ℕ) (hj : j ≠ 0) : 4 / (2 * π * j) = 2 / π / j := by
  have : (j : ℝ) ≠ 0 := by exact_mod_cast hj
  field_simp
  ring

lemma nonstat_left_term (t : ℝ) (ht : 0 < t) (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) (ν : ℤ)
    (j : ℕ) (hj : (j : ℝ) ≤ t / (2 * π * b) - ν) :
    ‖phaseInt t (2 * π * ν) a b‖ ≤ if j = 0 then 12 * b / Real.sqrt t else 2 / π / j := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast (lt_of_lt_of_le ha hab)
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  split_ifs with h0
  · exact sd_bound t _ a b ht ha' hab'
  · have hjpos : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero h0
    have hm : 0 < 2 * π * (j : ℝ) := by positivity
    have heq : t / b - 2 * π * ν = 2 * π * (t / (2 * π * b) - ν) := by
      field_simp
    have := fd_bound t (2 * π * ν) a b (2 * π * j) ht ha' hab' hm (Or.inl (by
      rw [heq]; exact mul_le_mul_of_nonneg_left hj (by positivity)))
    rwa [fd_const j h0] at this

lemma nonstat_right_term (t : ℝ) (ht : 0 < t) (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) (ν : ℤ)
    (j : ℕ) (hj : (j : ℝ) ≤ ν - t / (2 * π * a)) :
    ‖phaseInt t (2 * π * ν) a b‖ ≤ if j = 0 then 12 * b / Real.sqrt t else 2 / π / j := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  split_ifs with h0
  · exact sd_bound t _ a b ht ha' hab'
  · have hjpos : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero h0
    have hm : 0 < 2 * π * (j : ℝ) := by positivity
    have heq : t / a - 2 * π * ν = -(2 * π * (ν - t / (2 * π * a))) := by
      field_simp
      ring
    have := fd_bound t (2 * π * ν) a b (2 * π * j) ht ha' hab' hm (Or.inr (by
      rw [heq, neg_le_neg_iff]; exact mul_le_mul_of_nonneg_left hj (by positivity)))
    rwa [fd_const j h0] at this

lemma nonstat_left (t : ℝ) (ht : 0 < t) (a b K : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ ν ∈ (Finset.Icc (-(K : ℤ)) K).filter (fun ν : ℤ => (ν : ℝ) < t / (2 * π * b)),
        ‖phaseInt t (2 * π * ν) a b‖ ≤
      12 * b / Real.sqrt t + 2 / π * (1 + Real.log (2 * K : ℕ)) := by
  set α := t / (2 * π * b) with hα
  set M : ℤ := min (⌈α⌉ - 1) K with hM
  have hMα : (M : ℝ) < α := by
    have h1 : M ≤ ⌈α⌉ - 1 := min_le_left _ _
    have h2 : (M : ℝ) ≤ (⌈α⌉ : ℝ) - 1 := by exact_mod_cast h1
    linarith [Int.ceil_lt_add_one α]
  have hle : ∀ ν ∈ (Finset.Icc (-(K : ℤ)) K).filter (fun ν : ℤ => (ν : ℝ) < α),
      -(K : ℤ) ≤ ν ∧ ν ≤ M := by
    intro ν hν
    rw [Finset.mem_filter, Finset.mem_Icc] at hν
    have : ν < ⌈α⌉ := Int.lt_ceil.mpr hν.2
    exact ⟨hν.1.1, le_min (by omega) hν.1.2⟩
  apply sum_harm _ (fun ν => (M - ν).toNat) _ (2 * K)
  · intro ν hν
    have := hle ν hν
    have : M ≤ K := min_le_right _ _
    omega
  · positivity
  · positivity
  · intro ν hν
    apply nonstat_left_term t ht a b ha hab ν
    have h := hle ν hν
    have hz : (((M - ν).toNat : ℕ) : ℤ) = M - ν := Int.toNat_of_nonneg (by omega)
    have hr : (((M - ν).toNat : ℕ) : ℝ) = (M : ℝ) - ν := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hz
      push_cast at this
      exact this
    rw [hr]
    linarith
  · intro x hx y hy hxy
    have := hle x hx
    have := hle y hy
    simp only at hxy
    omega

lemma nonstat_right (t : ℝ) (ht : 0 < t) (a b K : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ ν ∈ (Finset.Icc (-(K : ℤ)) K).filter (fun ν : ℤ => t / (2 * π * a) < (ν : ℝ)),
        ‖phaseInt t (2 * π * ν) a b‖ ≤
      12 * b / Real.sqrt t + 2 / π * (1 + Real.log (2 * K : ℕ)) := by
  set β := t / (2 * π * a) with hβ
  set M : ℤ := max (⌊β⌋ + 1) (-(K : ℤ)) with hM
  have hMβ : β < (M : ℝ) := by
    have h1 : ⌊β⌋ + 1 ≤ M := le_max_left _ _
    have h2 : (⌊β⌋ : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast h1
    linarith [Int.lt_floor_add_one β]
  have hle : ∀ ν ∈ (Finset.Icc (-(K : ℤ)) K).filter (fun ν : ℤ => β < (ν : ℝ)),
      M ≤ ν ∧ ν ≤ K := by
    intro ν hν
    rw [Finset.mem_filter, Finset.mem_Icc] at hν
    have : ⌊β⌋ < ν := Int.floor_lt.mpr hν.2
    exact ⟨max_le (by omega) hν.1.1, hν.1.2⟩
  apply sum_harm _ (fun ν => (ν - M).toNat) _ (2 * K)
  · intro ν hν
    have := hle ν hν
    have : -(K : ℤ) ≤ M := le_max_right _ _
    omega
  · positivity
  · positivity
  · intro ν hν
    apply nonstat_right_term t ht a b ha hab ν
    have h := hle ν hν
    have hz : (((ν - M).toNat : ℕ) : ℤ) = ν - M := Int.toNat_of_nonneg (by omega)
    have hr : (((ν - M).toNat : ℕ) : ℝ) = (ν : ℝ) - M := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hz
      push_cast at this
      exact this
    rw [hr]
    linarith
  · intro x hx y hy hxy
    have := hle x hx
    have := hle y hy
    simp only at hxy
    omega

theorem nonstat_sum (t : ℝ) (ht : 0 < t) (a b K : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ ν ∈ (Finset.Icc (-(K : ℤ)) K).filter (fun ν => ¬ InWindow t a b ν),
        ‖phaseInt t (2 * π * ν) a b‖ ≤
      30 * b / Real.sqrt t + 4 * (1 + Real.log (2 * K + 1)) := by
  set S1 := (Finset.Icc (-(K : ℤ)) K).filter (fun ν : ℤ => (ν : ℝ) < t / (2 * π * b)) with hS1
  set S2 := (Finset.Icc (-(K : ℤ)) K).filter (fun ν : ℤ => t / (2 * π * a) < (ν : ℝ)) with hS2
  set F : ℤ → ℝ := fun ν => ‖phaseInt t (2 * π * ν) a b‖ with hF
  have hsub : (Finset.Icc (-(K : ℤ)) K).filter (fun ν => ¬ InWindow t a b ν) ⊆ S1 ∪ S2 := by
    intro ν hν
    rw [Finset.mem_filter] at hν
    unfold InWindow at hν
    rw [Finset.mem_union, hS1, hS2, Finset.mem_filter, Finset.mem_filter]
    by_cases h : (ν : ℝ) < t / (2 * π * b)
    · exact Or.inl ⟨hν.1, h⟩
    · right
      refine ⟨hν.1, ?_⟩
      by_contra h'
      exact hν.2 ⟨not_lt.mp h, not_lt.mp h'⟩
  have h1 : ∑ ν ∈ (Finset.Icc (-(K : ℤ)) K).filter (fun ν => ¬ InWindow t a b ν), F ν ≤
      ∑ ν ∈ S1, F ν + ∑ ν ∈ S2, F ν := by
    refine (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => norm_nonneg _)).trans ?_
    rw [← sum_union_inter]
    have : 0 ≤ ∑ ν ∈ S1 ∩ S2, F ν := sum_nonneg (fun _ _ => norm_nonneg _)
    linarith
  have hL := nonstat_left t ht a b K ha hab
  have hR := nonstat_right t ht a b K ha hab
  have hlog0 : 0 ≤ Real.log ((2 * K : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hlog1 : Real.log ((2 * K : ℕ) : ℝ) ≤ Real.log (2 * K + 1) :=
    log_nat_le _ _ (by have : (0:ℝ) ≤ K := Nat.cast_nonneg K; linarith) (by push_cast; linarith)
  have hpi : 2 / π ≤ 1 := by
    rw [div_le_one Real.pi_pos]; linarith [Real.pi_gt_three]
  have hX : 2 / π * (1 + Real.log ((2 * K : ℕ) : ℝ)) ≤ 2 * (1 + Real.log (2 * K + 1)) := by
    have : 2 / π * (1 + Real.log ((2 * K : ℕ) : ℝ)) ≤ 1 * (1 + Real.log ((2 * K : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hpi (by linarith)
    linarith
  have hb : 0 ≤ (b : ℝ) / Real.sqrt t := by positivity
  have e1 : 12 * (b : ℝ) / Real.sqrt t = 12 * (b / Real.sqrt t) := by ring
  have e2 : 30 * (b : ℝ) / Real.sqrt t = 30 * (b / Real.sqrt t) := by ring
  simp only [hF] at h1
  linarith

end GuthMaynard.BProc.PartC
end

section
open Complex Real MeasureTheory intervalIntegral Finset
namespace GuthMaynard.BProc
alias nonstat_sum := GuthMaynard.BProc.PartC.nonstat_sum

alias window_sum_eq := GuthMaynard.BProc.PartC.window_sum_eq

end GuthMaynard.BProc
end

section
open Complex Real MeasureTheory intervalIntegral Finset
namespace GuthMaynard.BProc.PartC
open GuthMaynard.BProc
/-! ### stationary frequencies -/
lemma stat_left_term (t : ℝ) (ht : 0 < t) (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) (ν : ℕ)
    (hν1 : t / (2 * π * b) ≤ ν) (j : ℕ) (hj : (j : ℝ) ≤ t / (2 * π * a) - ν) :
    (1 / (ν : ℝ)) * ‖phaseInt t (2 * π) (t * a / (2 * π * b)) (ν * a)‖ ≤
      if j = 0 then 12 * a / Real.sqrt t else 2 / π / j := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast (lt_of_lt_of_le ha hab)
  have hα : 0 < t / (2 * π * b) := by positivity
  have hν : (0 : ℝ) < ν := lt_of_lt_of_le hα hν1
  have hA : 0 < t * a / (2 * π * b) := by positivity
  have hAν : t * a / (2 * π * b) ≤ ν * a := by
    have : t * a / (2 * π * b) = t / (2 * π * b) * a := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right hν1 ha'.le
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  split_ifs with h0
  · have := sd_bound t (2 * π) _ _ ht hA hAν
    calc (1 / (ν : ℝ)) * ‖phaseInt t (2 * π) (t * a / (2 * π * b)) (ν * a)‖
        ≤ (1 / (ν : ℝ)) * (12 * (ν * a) / Real.sqrt t) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 12 * a / Real.sqrt t := by field_simp
  · have hjpos : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero h0
    have hm : 0 < 2 * π / ν * (j : ℝ) := by positivity
    have heq : t / (ν * a) - 2 * π = 2 * π / ν * (t / (2 * π * a) - ν) := by
      field_simp
    have := fd_bound t (2 * π) _ _ (2 * π / ν * j) ht hA hAν hm (Or.inl (by
      rw [heq]; exact mul_le_mul_of_nonneg_left hj (by positivity)))
    calc (1 / (ν : ℝ)) * ‖phaseInt t (2 * π) (t * a / (2 * π * b)) (ν * a)‖
        ≤ (1 / (ν : ℝ)) * (4 / (2 * π / ν * j)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 / π / j := by field_simp; ring

lemma stat_right_term (t : ℝ) (ht : 0 < t) (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) (ν : ℕ)
    (hν1 : t / (2 * π * b) ≤ ν) (hνβ : (ν : ℝ) ≤ t / (2 * π * a)) (j : ℕ)
    (hj : (j : ℝ) ≤ ν - t / (2 * π * b)) :
    (1 / (ν : ℝ)) * ‖phaseInt t (2 * π) (ν * b) (t * b / (2 * π * a))‖ ≤
      if j = 0 then 12 * (b : ℝ) ^ 2 / (a * Real.sqrt t) else 2 / π / j := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast (lt_of_lt_of_le ha hab)
  have hα : 0 < t / (2 * π * b) := by positivity
  have hν : (0 : ℝ) < ν := lt_of_lt_of_le hα hν1
  have hνb : (0 : ℝ) < ν * b := by positivity
  have hBν : (ν : ℝ) * b ≤ t * b / (2 * π * a) := by
    have : t * b / (2 * π * a) = t / (2 * π * a) * b := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right hνβ hb'.le
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  split_ifs with h0
  · have := sd_bound t (2 * π) _ _ ht hνb hBν
    have ht2 : t ≤ 2 * π * b * ν := by
      rw [div_le_iff₀ (by positivity)] at hν1; linarith
    calc (1 / (ν : ℝ)) * ‖phaseInt t (2 * π) (ν * b) (t * b / (2 * π * a))‖
        ≤ (1 / (ν : ℝ)) * (12 * (t * b / (2 * π * a)) / Real.sqrt t) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 12 * (t * b / (2 * π * a * ν)) / Real.sqrt t := by field_simp
      _ ≤ 12 * ((b : ℝ) ^ 2 / a) / Real.sqrt t := by
          have hk : t * b / (2 * π * a * ν) ≤ (b : ℝ) ^ 2 / a := by
            rw [div_le_div_iff₀ (by positivity) ha']
            have : t * b * a ≤ 2 * π * b * ν * (b * a) := by
              have := mul_le_mul_of_nonneg_right ht2 (by positivity : (0 : ℝ) ≤ b * a)
              linarith
            nlinarith
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hk (by norm_num)) hs.le
      _ = 12 * (b : ℝ) ^ 2 / (a * Real.sqrt t) := by field_simp
  · have hjpos : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero h0
    have hm : 0 < 2 * π / ν * (j : ℝ) := by positivity
    have heq : t / (ν * b) - 2 * π = -(2 * π / ν * (ν - t / (2 * π * b))) := by
      field_simp
      ring
    have := fd_bound t (2 * π) _ _ (2 * π / ν * j) ht hνb hBν hm (Or.inr (by
      rw [heq, neg_le_neg_iff]; exact mul_le_mul_of_nonneg_left hj (by positivity)))
    calc (1 / (ν : ℝ)) * ‖phaseInt t (2 * π) (ν * b) (t * b / (2 * π * a))‖
        ≤ (1 / (ν : ℝ)) * (4 / (2 * π / ν * j)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 / π / j := by field_simp; ring

lemma norm_weight (t : ℝ) (ν : ℕ) (hν : 1 ≤ ν) :
    ‖(1 / (ν : ℂ)) * (ν : ℂ) ^ (-(t : ℂ) * I)‖ = 1 / (ν : ℝ) := by
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
  simp

theorem stat_sum (t : ℝ) (ht : 0 < t) (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖∑ ν ∈ Finset.Icc ⌈t / (2 * π * b)⌉₊ ⌊t / (2 * π * a)⌋₊, phaseInt t (2 * π * ν) a b
        - phaseInt t (2 * π) (t * a / (2 * π * b)) (t * b / (2 * π * a)) *
          ∑ ν ∈ Finset.Icc ⌈t / (2 * π * b)⌉₊ ⌊t / (2 * π * a)⌋₊,
            (1 / (ν : ℂ)) * (ν : ℂ) ^ (-(t : ℂ) * I)‖ ≤
      30 * (b : ℝ) ^ 2 / (a * Real.sqrt t) + 6 * (1 + Real.log (t + 2)) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast (lt_of_lt_of_le ha hab)
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  set α := t / (2 * π * b) with hαdef
  set β := t / (2 * π * a) with hβdef
  have hα : 0 < α := by positivity
  have hβ : 0 ≤ β := by positivity
  set I0 := Finset.Icc ⌈α⌉₊ ⌊β⌋₊ with hI0
  set A := t * a / (2 * π * b) with hAdef
  set B := t * b / (2 * π * a) with hBdef
  set G := phaseInt t (2 * π) with hG
  set w : ℕ → ℂ := fun ν => (1 / (ν : ℂ)) * (ν : ℂ) ^ (-(t : ℂ) * I) with hw
  have hmem : ∀ ν ∈ I0, 1 ≤ ν ∧ α ≤ ν ∧ (ν : ℝ) ≤ β ∧ ⌈α⌉₊ ≤ ν ∧ ν ≤ ⌊β⌋₊ := by
    intro ν hν
    rw [hI0, Finset.mem_Icc] at hν
    have h1 : 0 < ⌈α⌉₊ := Nat.ceil_pos.mpr hα
    exact ⟨by omega, Nat.ceil_le.mp hν.1, (Nat.le_floor_iff hβ).mp hν.2, hν.1, hν.2⟩
  have hkey : ∀ ν ∈ I0, phaseInt t (2 * π * ν) a b - G A B * w ν =
      -(w ν * (G A (ν * a) + G (ν * b) B)) := by
    intro ν hν
    obtain ⟨h1, h2, h3, -, -⟩ := hmem ν hν
    have hν0 : (0 : ℝ) < ν := by exact_mod_cast h1
    have hA : 0 < A := by positivity
    have hB : 0 < B := by positivity
    rw [rescale t a b ν h1]
    simp only [hw, hG]
    rw [phaseInt_split t (2 * π) A (ν * a) B hA (by positivity) hB,
      phaseInt_split t (2 * π) (ν * a) (ν * b) B (by positivity) (by positivity) hB]
    ring
  have hrw : (∑ ν ∈ I0, phaseInt t (2 * π * ν) a b) - G A B * ∑ ν ∈ I0, w ν =
      ∑ ν ∈ I0, -(w ν * (G A (ν * a) + G (ν * b) B)) := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl hkey
  have hnorm : ‖∑ ν ∈ I0, -(w ν * (G A (ν * a) + G (ν * b) B))‖ ≤
      ∑ ν ∈ I0, (1 / (ν : ℝ)) * ‖G A (ν * a)‖ + ∑ ν ∈ I0, (1 / (ν : ℝ)) * ‖G (ν * b) B‖ := by
    rw [← sum_add_distrib]
    refine (norm_sum_le _ _).trans (sum_le_sum (fun ν hν => ?_))
    rw [norm_neg, norm_mul, hw]
    simp only
    rw [norm_weight t ν (hmem ν hν).1, ← mul_add]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
  have hS1 : ∑ ν ∈ I0, (1 / (ν : ℝ)) * ‖G A (ν * a)‖ ≤
      12 * a / Real.sqrt t + 2 / π * (1 + Real.log ⌊β⌋₊) := by
    apply sum_harm I0 (fun ν => ⌊β⌋₊ - ν) _ ⌊β⌋₊
    · intro ν _; omega
    · positivity
    · positivity
    · intro ν hν
      obtain ⟨_, h2, _, _, h5⟩ := hmem ν hν
      apply stat_left_term t ht a b ha hab ν h2
      rw [Nat.cast_sub h5]
      linarith [Nat.floor_le hβ]
    · intro x hx y hy hxy
      have := (hmem x hx).2.2.2.2
      have := (hmem y hy).2.2.2.2
      simp only at hxy
      omega
  have hS2 : ∑ ν ∈ I0, (1 / (ν : ℝ)) * ‖G (ν * b) B‖ ≤
      12 * (b : ℝ) ^ 2 / (a * Real.sqrt t) + 2 / π * (1 + Real.log ⌊β⌋₊) := by
    apply sum_harm I0 (fun ν => ν - ⌈α⌉₊) _ ⌊β⌋₊
    · intro ν hν; have := (hmem ν hν).2.2.2.2; omega
    · positivity
    · positivity
    · intro ν hν
      obtain ⟨_, h2, h3, h4, _⟩ := hmem ν hν
      apply stat_right_term t ht a b ha hab ν h2 h3
      rw [Nat.cast_sub h4]
      linarith [Nat.le_ceil α]
    · intro x hx y hy hxy
      have := (hmem x hx).2.2.2.1
      have := (hmem y hy).2.2.2.1
      simp only at hxy
      omega
  have hlog : Real.log ⌊β⌋₊ ≤ Real.log (t + 2) := by
    apply log_nat_le _ _ (by linarith)
    have h1 : β ≤ t := by
      rw [hβdef]
      apply div_le_self ht.le
      have : (1 : ℝ) ≤ 2 * π := by linarith [Real.pi_gt_three]
      nlinarith
    linarith [Nat.floor_le hβ]
  have hlog0 : 0 ≤ Real.log ⌊β⌋₊ := Real.log_natCast_nonneg _
  have hpi : 2 / π ≤ 1 := by
    rw [div_le_one Real.pi_pos]; linarith [Real.pi_gt_three]
  have hX : 2 / π * (1 + Real.log ⌊β⌋₊) ≤ 1 * (1 + Real.log ⌊β⌋₊) :=
    mul_le_mul_of_nonneg_right hpi (by linarith)
  have hab2 : 12 * (a : ℝ) / Real.sqrt t ≤ 12 * (b : ℝ) ^ 2 / (a * Real.sqrt t) := by
    rw [div_le_div_iff₀ hs (by positivity)]
    have : (a : ℝ) * a ≤ b ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_right this hs.le
    nlinarith
  have hq : 0 ≤ 12 * (b : ℝ) ^ 2 / (a * Real.sqrt t) := by positivity
  have he : 30 * (b : ℝ) ^ 2 / (a * Real.sqrt t) =
      (30 / 12) * (12 * (b : ℝ) ^ 2 / (a * Real.sqrt t)) := by ring
  rw [hrw]
  linarith

end GuthMaynard.BProc.PartC
end

section
open Complex Real MeasureTheory intervalIntegral Finset
namespace GuthMaynard.BProc
alias stat_sum := GuthMaynard.BProc.PartC.stat_sum

end GuthMaynard.BProc
end

section
open Complex Real MeasureTheory intervalIntegral Finset
namespace GuthMaynard.BProc.PartD
open GuthMaynard.BProc
lemma abel_aux (L R0 : ℕ) (w : ℕ → ℝ) (hw : ∀ n, L ≤ n → n < R0 → w (n + 1) ≤ w n)
    (z : ℕ → ℂ) (B : ℝ) (hB : ∀ n, L ≤ n → n ≤ R0 → ‖∑ ν ∈ Icc L n, z ν‖ ≤ B) :
    ∀ R, L ≤ R → R ≤ R0 →
      ‖∑ ν ∈ Icc L R, (w ν : ℂ) * z ν - (w R : ℂ) * ∑ ν ∈ Icc L R, z ν‖ ≤ (w L - w R) * B := by
  intro R hLR
  induction R, hLR using Nat.le_induction with
  | base => intro _; simp
  | succ R hLR ih =>
    intro hR
    have key : ∑ ν ∈ Icc L (R + 1), (w ν : ℂ) * z ν - (w (R + 1) : ℂ) * ∑ ν ∈ Icc L (R + 1), z ν
        = (∑ ν ∈ Icc L R, (w ν : ℂ) * z ν - (w R : ℂ) * ∑ ν ∈ Icc L R, z ν)
          + ((w R - w (R + 1) : ℝ) : ℂ) * ∑ ν ∈ Icc L R, z ν := by
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
      push_cast; ring
    rw [key]
    have h1 := ih (by omega)
    have h2 := hB R hLR (by omega)
    have h3 := hw R hLR (by omega)
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ (w L - w R) * B + (w R - w (R + 1)) * B := by
        apply add_le_add h1
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
        gcongr
      _ = _ := by ring

theorem abel_dec (L R : ℕ) (hL : 1 ≤ L) (z : ℕ → ℂ) :
    ∃ M : ℕ, L ≤ M ∧ M ≤ max L R ∧
      ‖∑ ν ∈ Finset.Icc L R, (1 / (ν : ℂ)) * z ν‖ ≤ (1 / (L : ℝ)) * ‖∑ ν ∈ Finset.Icc L M, z ν‖ := by
  rcases lt_or_ge R L with h | h
  · refine ⟨L, le_rfl, le_max_left _ _, ?_⟩
    rw [Finset.Icc_eq_empty (by omega)]; simp; positivity
  · obtain ⟨M, hM, hmax⟩ :=
      Finset.exists_max_image (Icc L R) (fun n => ‖∑ ν ∈ Icc L n, z ν‖) (Finset.nonempty_Icc.2 h)
    rw [Finset.mem_Icc] at hM
    refine ⟨M, hM.1, by rw [max_eq_right h]; exact hM.2, ?_⟩
    set B := ‖∑ ν ∈ Icc L M, z ν‖
    have hw : ∀ n, L ≤ n → n < R → (fun n : ℕ => 1 / (n : ℝ)) (n + 1) ≤ (fun n : ℕ => 1 / (n : ℝ)) n := by
      intro n hn _
      have : (1 : ℝ) ≤ n := by exact_mod_cast le_trans hL hn
      simp only
      gcongr; linarith
    have key := abel_aux L R (fun n : ℕ => 1 / (n : ℝ)) hw z B
      (fun n h1 h2 => hmax n (mem_Icc.2 ⟨h1, h2⟩)) R h le_rfl
    have hsum : ∑ ν ∈ Icc L R, (1 / (ν : ℂ)) * z ν =
        (∑ ν ∈ Icc L R, ((1 / (ν : ℝ) : ℝ) : ℂ) * z ν
          - ((1 / (R : ℝ) : ℝ) : ℂ) * ∑ ν ∈ Icc L R, z ν)
        + ((1 / (R : ℝ) : ℝ) : ℂ) * ∑ ν ∈ Icc L R, z ν := by
      push_cast; ring
    rw [hsum]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ (1 / (L : ℝ) - 1 / (R : ℝ)) * B + 1 / (R : ℝ) * B := by
         apply add_le_add key
         rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
         gcongr; exact hmax R (mem_Icc.2 ⟨h, le_rfl⟩)
      _ = _ := by ring

end GuthMaynard.BProc.PartD
end

section
open Complex Real MeasureTheory intervalIntegral Finset
namespace GuthMaynard.BProc
/-! ### Part D: Abel summation and the assembly -/

end GuthMaynard.BProc
end

section
open Complex Real MeasureTheory intervalIntegral Finset
namespace GuthMaynard.BProc.PartD
open GuthMaynard.BProc
lemma cpow_eq_ph (t : ℝ) (n : ℕ) (hn : 1 ≤ n) : (n : ℂ) ^ ((t : ℂ) * I) = ph t 0 n := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [cpow_def_of_ne_zero hn0, ph]
  congr 1
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (by positivity)]
  push_cast; ring

lemma norm_ph (t c x : ℝ) : ‖ph t c x‖ = 1 := Complex.norm_exp_ofReal_mul_I _

lemma sum_eq_ph (t : ℝ) (N : ℕ) (hN : 2 ≤ N) :
    ∑ n ∈ Icc N (2 * N), (n : ℂ) ^ ((t : ℂ) * I) = ∑ n ∈ Ioc (N - 1) (2 * N), ph t 0 n := by
  have : Ioc (N - 1) (2 * N) = Icc N (2 * N) := by
    ext n; simp only [mem_Ioc, mem_Icc]; omega
  rw [this]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rw [mem_Icc] at hn
  exact cpow_eq_ph t n (by omega)

lemma cpow_neg_eq_conj (t : ℝ) (ν : ℕ) :
    (ν : ℂ) ^ (-(t : ℂ) * I) = (starRingEnd ℂ) ((ν : ℂ) ^ ((t : ℂ) * I)) := by
  have h := Complex.conj_cpow (ν : ℂ) (-(t : ℂ) * I) (by rw [Complex.natCast_arg]; positivity)
  rw [Complex.conj_natCast] at h
  rw [h]
  congr 2
  simp [Complex.conj_ofReal]

lemma norm_sum_neg (t : ℝ) (L M : ℕ) :
    ‖∑ ν ∈ Icc L M, (ν : ℂ) ^ (-(t : ℂ) * I)‖ = ‖∑ ν ∈ Icc L M, (ν : ℂ) ^ ((t : ℂ) * I)‖ := by
  simp_rw [cpow_neg_eq_conj, ← map_sum, Complex.norm_conj]

lemma main_ge_two (N : ℕ) (hN : 2 ≤ N) (t : ℝ) (ht : 10 * (N : ℝ) ≤ t) :
    ∃ L M : ℕ, 1 ≤ L ∧ t / (8 * Real.pi * N) ≤ L ∧ (M : ℝ) ≤ t / (Real.pi * N) + 1 ∧
      ‖∑ n ∈ Finset.Icc N (2 * N), (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ≤
        300 * (N / Real.sqrt t * ‖∑ m ∈ Finset.Icc L M, (m : ℂ) ^ ((t : ℂ) * Complex.I)‖ +
          N / Real.sqrt t + Real.log (N * t + 2)) := by
  have hN1 : (2:ℝ) ≤ N := by exact_mod_cast hN
  have ht0 : 0 < t := by linarith
  obtain ⟨a, ha_def⟩ : ∃ a : ℕ, a = N - 1 := ⟨_, rfl⟩
  obtain ⟨b, hb_def⟩ : ∃ b : ℕ, b = 2 * N := ⟨_, rfl⟩
  obtain ⟨K, hK_def⟩ : ∃ K : ℕ, K = 9 * ⌈t ^ 2⌉₊ + 1 := ⟨_, rfl⟩
  have ha : 1 ≤ a := by omega
  have hab : a ≤ b := by omega
  have hK1 : 1 ≤ K := by omega
  have haR : (a : ℝ) = N - 1 := by rw [ha_def, Nat.cast_sub (by omega)]; simp
  have hbR : (b : ℝ) = 2 * N := by rw [hb_def]; push_cast; ring
  have haR0 : (0:ℝ) < a := by rw [haR]; linarith
  have hbR0 : (0:ℝ) < b := by rw [hbR]; linarith
  have hKR : 9 * t ^ 2 + 1 ≤ (K : ℝ) := by
    rw [hK_def]; push_cast; have := Nat.le_ceil (t ^ 2); linarith
  have hKR' : (K : ℝ) ≤ 9 * t ^ 2 + 10 := by
    rw [hK_def]; push_cast; have := Nat.ceil_lt_add_one (sq_nonneg t); linarith
  have hKwin : t / (2 * π * a) ≤ K := by
    have : t / (2 * π * a) ≤ t := by
      rw [div_le_iff₀ (by positivity)]
      have : (1:ℝ) ≤ a := by exact_mod_cast ha
      nlinarith [Real.pi_gt_three, mul_le_mul_of_nonneg_left
        (show (1:ℝ) ≤ 2 * π * a by nlinarith [Real.pi_gt_three]) ht0.le]
    nlinarith
  have hLpos : 0 < t / (2 * π * b) := by positivity
  obtain ⟨L, hL_def⟩ : ∃ L : ℕ, L = ⌈t / (2 * π * b)⌉₊ := ⟨_, rfl⟩
  obtain ⟨R, hR_def⟩ : ∃ R : ℕ, R = ⌊t / (2 * π * a)⌋₊ := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (by rw [hL_def]; exact (Nat.ceil_pos.2 hLpos).ne')
  have hLge : t / (2 * π * b) ≤ L := by rw [hL_def]; exact Nat.le_ceil _
  obtain ⟨M, hLM, hMmax, habel⟩ := abel_dec L R hL1 (fun ν => (ν : ℂ) ^ (-(t : ℂ) * I))
  refine ⟨L, M, hL1, ?_, ?_, ?_⟩
  · refine le_trans ?_ hLge
    rw [div_le_div_iff_of_pos_left ht0 (by positivity) (by positivity), hbR]
    nlinarith [Real.pi_pos]
  · have hLle : (L:ℝ) ≤ t / (Real.pi * N) + 1 := by
      have := Nat.ceil_lt_add_one hLpos.le
      rw [← hL_def] at this
      have : t / (2 * π * b) ≤ t / (π * N) := by
        rw [div_le_div_iff_of_pos_left ht0 (by positivity) (by positivity), hbR]
        nlinarith [Real.pi_pos]
      linarith
    have hRle : (R:ℝ) ≤ t / (Real.pi * N) + 1 := by
      have := Nat.floor_le (show 0 ≤ t / (2 * π * a) by positivity)
      rw [← hR_def] at this
      have : t / (2 * π * a) ≤ t / (π * N) := by
        rw [div_le_div_iff_of_pos_left ht0 (by positivity) (by positivity), haR]
        nlinarith [Real.pi_pos]
      linarith
    have : (M:ℝ) ≤ max (L:ℝ) R := by exact_mod_cast hMmax
    rcases le_total (L:ℝ) R with h | h
    · rw [max_eq_right h] at this; linarith
    · rw [max_eq_left h] at this; linarith
  · -- the decomposition
    have hS : ∑ n ∈ Icc N (2 * N), (n : ℂ) ^ ((t : ℂ) * I) = ∑ n ∈ Ioc a b, ph t 0 n := by
      rw [ha_def, hb_def]; exact sum_eq_ph t N hN
    have h1 : phaseInt t 0 a b + ∑ ν ∈ (Icc (-(K:ℤ)) K).erase 0, phaseInt t (2 * π * ν) a b
        = ∑ ν ∈ Icc (-(K:ℤ)) K, phaseInt t (2 * π * ν) a b := by
      rw [← Finset.add_sum_erase _ _ (show (0:ℤ) ∈ Icc (-(K:ℤ)) K by simp)]; simp
    have h2 : ∑ ν ∈ Icc (-(K:ℤ)) K, phaseInt t (2 * π * ν) a b
        = ∑ ν ∈ (Finset.Icc (-(K : ℤ)) K).filter (fun ν => InWindow t a b ν),
            phaseInt t (2 * π * ν) a b
          + ∑ ν ∈ (Finset.Icc (-(K : ℤ)) K).filter (fun ν => ¬ InWindow t a b ν),
            phaseInt t (2 * π * ν) a b :=
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    have h3 := window_sum_eq t ht0 a b K ha hab hKwin (fun x => phaseInt t (2 * π * x) a b)
    beta_reduce at h3
    rw [← hL_def, ← hR_def] at h3
    have hdec : ∑ n ∈ Icc N (2 * N), (n : ℂ) ^ ((t : ℂ) * I) =
        phaseInt t (2 * π) (t * a / (2 * π * b)) (t * b / (2 * π * a)) *
            ∑ ν ∈ Icc L R, (1 / (ν : ℂ)) * (ν : ℂ) ^ (-(t : ℂ) * I)
          + (∑ ν ∈ Icc L R, phaseInt t (2 * π * ν) a b
              - phaseInt t (2 * π) (t * a / (2 * π * b)) (t * b / (2 * π * a)) *
                ∑ ν ∈ Icc L R, (1 / (ν : ℂ)) * (ν : ℂ) ^ (-(t : ℂ) * I))
          + ∑ ν ∈ (Finset.Icc (-(K : ℤ)) K).filter (fun ν => ¬ InWindow t a b ν),
              phaseInt t (2 * π * ν) a b
          + (∫ x in (a : ℝ)..b, sawTail K x * (((t / x : ℝ) : ℂ) * I * ph t 0 x))
          + (ph t 0 b - ph t 0 a) / 2 := by
      rw [hS, em_identity t a b ha hab, saw_expand t a b K ha hab]
      linear_combination h1 + h2 + h3
    rw [hdec]
    -- bounds
    have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
    have hA : 0 < t * a / (2 * π * b) := by positivity
    have hAB : t * a / (2 * π * b) ≤ t * b / (2 * π * a) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : (a:ℝ) ≤ b := by exact_mod_cast hab
      have : (a:ℝ) * a ≤ b * b := by nlinarith
      have := mul_le_mul_of_nonneg_left this (show 0 ≤ t * (2 * π) by positivity)
      nlinarith
    have hG := sd_bound t (2 * π) _ _ ht0 hA hAB
    have hSig : ‖∑ ν ∈ Icc L R, (1 / (ν : ℂ)) * (ν : ℂ) ^ (-(t : ℂ) * I)‖ ≤
        1 / (L : ℝ) * ‖∑ m ∈ Finset.Icc L M, (m : ℂ) ^ ((t : ℂ) * Complex.I)‖ := by
      rw [← norm_sum_neg]; exact habel
    have hLinv : 1 / (L : ℝ) ≤ 2 * π * b / t := by
      have := one_div_le_one_div_of_le hLpos hLge
      rwa [one_div_div] at this
    have hE := stat_sum t ht0 a b ha hab
    rw [← hL_def, ← hR_def] at hE
    have hnon := (norm_sum_le _ _).trans (nonstat_sum t ht0 a b K ha hab)
    have htail := tail_term_le t ht0 a b K ha hab hK1
    have hF : ‖(ph t 0 b - ph t 0 a) / 2‖ ≤ 1 := by
      rw [norm_div]
      have := norm_sub_le (ph t 0 b) (ph t 0 a)
      rw [norm_ph, norm_ph] at this
      simp only [Complex.norm_ofNat]
      linarith
    -- real arithmetic
    set s := Real.sqrt t with hs_def
    have hss : s * s = t := Real.mul_self_sqrt ht0.le
    set D := ‖∑ m ∈ Finset.Icc L M, (m : ℂ) ^ ((t : ℂ) * Complex.I)‖ with hD_def
    have hD : 0 ≤ D := norm_nonneg _
    set ℓ := Real.log (N * t + 2) with hℓ_def
    have htN : t ≤ N * t := le_mul_of_one_le_left ht0.le (by linarith)
    have hx : (12:ℝ) ≤ N * t + 2 := by linarith
    have hℓ1 : 1 ≤ ℓ := by
      rw [hℓ_def, Real.le_log_iff_exp_le (by positivity)]
      have := Real.exp_one_lt_d9; linarith
    have hlt : Real.log (t + 2) ≤ ℓ := Real.log_le_log (by positivity) (by linarith)
    have hlK : Real.log (2 * K + 1) ≤ 4 * ℓ := by
      have h4 : 4 * ℓ = Real.log ((N * t + 2) ^ 4) := by
        rw [Real.log_pow, hℓ_def]; push_cast; ring
      rw [h4]
      apply Real.log_le_log (by positivity)
      have hx2 : t ^ 2 ≤ (N * t + 2) ^ 2 := pow_le_pow_left₀ ht0.le (by linarith) 2
      have hx144 : (12:ℝ) ^ 2 ≤ (N * t + 2) ^ 2 := pow_le_pow_left₀ (by norm_num) hx 2
      have ht2 : (10:ℝ) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
      have : (N * t + 2) ^ 4 = (N * t + 2) ^ 2 * (N * t + 2) ^ 2 := by ring
      rw [this]
      have := mul_le_mul hx144 hx2 (sq_nonneg t) (by positivity)
      linarith
    have hsK : 3 * t ≤ Real.sqrt K :=
      (Real.le_sqrt (by positivity) (by positivity)).2 (by rw [mul_pow]; linarith)
    have htail1 : t / a * (b - a) / Real.sqrt K ≤ 1 := by
      rw [div_mul_eq_mul_div, div_div, div_le_one (by positivity), haR, hbR]
      have := mul_le_mul_of_nonneg_left hsK haR0.le
      rw [haR] at this
      linarith [mul_le_mul_of_nonneg_left hN1 ht0.le]
    have hq : (b:ℝ) ^ 2 / (a * s) ≤ 8 * (N / s) := by
      rw [div_le_iff₀ (by positivity)]
      have : 8 * (N / s) * (a * s) = 8 * N * a := by field_simp
      rw [this, haR, hbR]
      linarith [mul_le_mul_of_nonneg_left hN1 (show (0:ℝ) ≤ N by positivity)]
    have hX1 : ‖phaseInt t (2 * π) (t * a / (2 * π * b)) (t * b / (2 * π * a))‖ *
        ‖∑ ν ∈ Icc L R, (1 / (ν : ℂ)) * (ν : ℂ) ^ (-(t : ℂ) * I)‖ ≤ 96 * (N / s) * D := by
      calc _ ≤ 12 * (t * b / (2 * π * a)) / s * (1 / (L:ℝ) * D) :=
            mul_le_mul hG hSig (norm_nonneg _) (by positivity)
        _ ≤ 12 * (t * b / (2 * π * a)) / s * (2 * π * b / t * D) := by gcongr
        _ = 12 * ((b:ℝ) ^ 2 / (a * s)) * D := by
            field_simp
        _ ≤ 12 * (8 * (N / s)) * D := by gcongr
        _ = 96 * (N / s) * D := by ring
    have hb' : 30 * (b:ℝ) / s = 60 * (N / s) := by rw [hbR]; ring
    have hNs : 0 ≤ (N:ℝ) / s := by positivity
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ _ := add_le_add_left (norm_add_le _ _) _
      _ ≤ _ := add_le_add_left (add_le_add_left (norm_add_le _ _) _) _
      _ ≤ _ := add_le_add_left (add_le_add_left (add_le_add_left (norm_add_le _ _) _) _) _
      _ ≤ 300 * (N / s * D + N / s + ℓ) := by
        rw [norm_mul]
        have hq' : 30 * (b:ℝ) ^ 2 / (a * s) ≤ 240 * (N / s) := by
          calc 30 * (b:ℝ) ^ 2 / (a * s) = 30 * ((b:ℝ) ^ 2 / (a * s)) := by ring
            _ ≤ 30 * (8 * (N / s)) := by gcongr
            _ = 240 * (N / s) := by ring
        linarith [htail.trans htail1, mul_nonneg hNs hD]

lemma main_one (N : ℕ) (hN : N = 1) (t : ℝ) (ht : 10 * (N : ℝ) ≤ t) :
    ∃ L M : ℕ, 1 ≤ L ∧ t / (8 * Real.pi * N) ≤ L ∧ (M : ℝ) ≤ t / (Real.pi * N) + 1 ∧
      ‖∑ n ∈ Finset.Icc N (2 * N), (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ≤
        300 * (N / Real.sqrt t * ‖∑ m ∈ Finset.Icc L M, (m : ℂ) ^ ((t : ℂ) * Complex.I)‖ +
          N / Real.sqrt t + Real.log (N * t + 2)) := by
  subst hN
  simp only [Nat.cast_one, mul_one, one_mul] at ht ⊢
  have ht0 : 0 < t := by linarith
  have hpos : 0 < t / (8 * Real.pi) := by positivity
  have hL1 : 1 ≤ ⌈t / (8 * Real.pi)⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hpos).ne'
  refine ⟨⌈t / (8 * Real.pi)⌉₊, 0, hL1, Nat.le_ceil _, by simp; positivity, ?_⟩
  rw [Finset.Icc_eq_empty (show ¬ (⌈t / (8 * Real.pi)⌉₊ ≤ 0) by omega),
    show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide]
  have h2 : ‖((2:ℕ) : ℂ) ^ ((t : ℂ) * I)‖ = 1 := by
    rw [Complex.norm_natCast_cpow_of_pos (by norm_num)]; simp
  have hlog : 1 ≤ Real.log (t + 2) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9; linarith
  have hs : 0 ≤ 1 / Real.sqrt t := by positivity
  rw [Finset.sum_pair (by norm_num)]
  have := norm_add_le (((1:ℕ) : ℂ) ^ ((t : ℂ) * I)) (((2:ℕ) : ℂ) ^ ((t : ℂ) * I))
  rw [h2] at this
  simp only [Nat.cast_one, Complex.one_cpow, norm_one, Finset.sum_empty, norm_zero,
    mul_zero, zero_add] at this ⊢
  push_cast at this ⊢
  nlinarith

theorem norm_dyadic_sum_cpow_le_dual_sum_dev :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ, 10 * N ≤ t →
      ∃ L M : ℕ, 1 ≤ L ∧ t / (8 * Real.pi * N) ≤ L ∧ (M : ℝ) ≤ t / (Real.pi * N) + 1 ∧
        ‖∑ n ∈ Finset.Icc N (2 * N), (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ≤
          C * (N / Real.sqrt t * ‖∑ m ∈ Finset.Icc L M, (m : ℂ) ^ ((t : ℂ) * Complex.I)‖ +
            N / Real.sqrt t + Real.log (N * t + 2)) := by
  refine ⟨300, by norm_num, fun N hN t ht => ?_⟩
  rcases eq_or_lt_of_le hN with h | h
  · exact main_one N h.symm t ht
  · exact main_ge_two N h t ht

end GuthMaynard.BProc.PartD
end

section
open Complex Real MeasureTheory intervalIntegral Finset
namespace GuthMaynard.BProc
alias norm_dyadic_sum_cpow_le_dual_sum_dev := GuthMaynard.BProc.PartD.norm_dyadic_sum_cpow_le_dual_sum_dev

end GuthMaynard.BProc
end

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ, 10 * N ≤ t →
      ∃ L M : ℕ, 1 ≤ L ∧ t / (8 * Real.pi * N) ≤ L ∧ (M : ℝ) ≤ t / (Real.pi * N) + 1 ∧
        ‖∑ n ∈ Finset.Icc N (2 * N), (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ≤
          C * (N / Real.sqrt t * ‖∑ m ∈ Finset.Icc L M, (m : ℂ) ^ ((t : ℂ) * Complex.I)‖ +
            N / Real.sqrt t + Real.log (N * t + 2)) :=
  GuthMaynard.BProc.norm_dyadic_sum_cpow_le_dual_sum_dev
