-- Prove2me | solution 1 for InhomMJPStrong.J1.erlang_central_moment
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T22:57:31.036602+00:00
-- url     : https://prove2.me/submissions/6d26f35d-f275-4aa5-b40e-0f315712e0f6

import Mathlib
import Definitions.Def_InhomMJPStrong_J1_Model

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace J1Erlang

section Alg
open PowerSeries

/-- Partial sums of `e⁻¹`: `d q = ∑_{k ≤ q} (-1)^k / k!` (normalised central moments of `Exp(1)`). -/
noncomputable def dd (q : ℕ) : ℝ := ∑ k ∈ Finset.range (q + 1), (-1 : ℝ) ^ k / (k.factorial : ℝ)

lemma dd_succ (q : ℕ) : dd (q + 1) = dd q + (-1 : ℝ) ^ (q + 1) / ((q + 1).factorial : ℝ) := by
  unfold dd; rw [Finset.sum_range_succ]

lemma dd_zero : dd 0 = 1 := by simp [dd]

lemma dd_one : dd 1 = 0 := by simp [dd, Finset.sum_range_succ]

lemma dd_rec (q : ℕ) : dd (q + 2) * (q + 2) - dd (q + 1) * (q + 1) = dd q := by
  have h1 := dd_succ (q + 1)
  have h2 := dd_succ q
  rw [h1, h2]
  have hf1 : ((q + 1 + 1).factorial : ℝ) = (q + 2) * ((q + 1).factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [hf1]
  have hpos : (0:ℝ) < ((q + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  field_simp
  ring

/-- The generating series `e^{-t}/(1-t)`. -/
noncomputable def Dser : PowerSeries ℝ := PowerSeries.mk dd

lemma Dser_ode : (1 - X) * d⁄dX ℝ Dser = X * Dser := by
  ext p
  rcases p with _ | q
  · rw [sub_mul, one_mul, map_sub, coeff_derivative, coeff_zero_X_mul, coeff_zero_X_mul]
    simp [Dser, coeff_mk, dd_one]
  · rw [sub_mul, one_mul, map_sub, coeff_derivative, coeff_succ_X_mul, coeff_derivative,
      coeff_succ_X_mul, Dser, coeff_mk, coeff_mk, coeff_mk]
    have := dd_rec q
    push_cast
    linarith

lemma pow_ode (m : ℕ) : (1 - X) * d⁄dX ℝ (Dser ^ m) = (m : PowerSeries ℝ) * X * Dser ^ m := by
  rcases m with _ | m
  · simp
  · rw [derivative_pow]
    simp only [Nat.add_sub_cancel]
    calc (1 - X) * ((↑(m + 1) : PowerSeries ℝ) * Dser ^ m * d⁄dX ℝ Dser)
        = (↑(m + 1) : PowerSeries ℝ) * Dser ^ m * ((1 - X) * d⁄dX ℝ Dser) := by ring
      _ = _ := by rw [Dser_ode]; ring

/-- Coefficient recursion `(p+1) b_{p+1} = p b_p + m b_{p-1}`. -/
lemma coeff_rec (m q : ℕ) :
    coeff (q + 2) (Dser ^ m) * (q + 2) = coeff (q + 1) (Dser ^ m) * (q + 1) +
      (m : ℝ) * coeff q (Dser ^ m) := by
  have h := congrArg (coeff (q + 1)) (pow_ode m)
  rw [sub_mul, one_mul, map_sub, coeff_derivative, coeff_succ_X_mul, coeff_derivative,
    mul_assoc, ← map_natCast (C (R := ℝ)), coeff_C_mul, coeff_succ_X_mul] at h
  push_cast at h
  linarith

lemma coeff_one_eq (m : ℕ) : coeff 1 (Dser ^ m) = 0 := by
  have h := congrArg (coeff 0) (pow_ode m)
  rw [sub_mul, one_mul, map_sub, coeff_derivative, mul_assoc, ← map_natCast (C (R := ℝ)),
    coeff_C_mul] at h
  simp at h
  simpa using h

lemma coeff_zero_eq (m : ℕ) : coeff 0 (Dser ^ m) = 1 := by
  rw [coeff_zero_eq_constantCoeff, map_pow]
  simp [Dser, dd_zero]

/-- Geometric partial sums `S h = ∑_{i ≤ h} m^i`. -/
noncomputable def S (m : ℝ) (h : ℕ) : ℝ := ∑ i ∈ Finset.range (h + 1), m ^ i

lemma S_mono {m : ℝ} (hm : 0 ≤ m) {a b : ℕ} (hab : a ≤ b) : S m a ≤ S m b :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
    fun i _ _ => pow_nonneg hm i

lemma mul_S_le {m : ℝ} (hm : 0 ≤ m) (h : ℕ) : m * S m h ≤ S m (h + 1) := by
  unfold S
  rw [Finset.sum_range_succ' (fun i => m ^ i) (h + 1), Finset.mul_sum]
  have : ∑ i ∈ Finset.range (h + 1), m * m ^ i = ∑ i ∈ Finset.range (h + 1), m ^ (i + 1) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [this]; simp

lemma coeff_bound (m : ℕ) : ∀ p : ℕ,
    0 ≤ coeff p (Dser ^ m) ∧ coeff p (Dser ^ m) ≤ S m (p / 2) := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    rcases p with _ | _ | q
    · rw [coeff_zero_eq]; simp [S]
    · rw [coeff_one_eq]; refine ⟨le_rfl, ?_⟩
      unfold S; exact Finset.sum_nonneg fun i _ => pow_nonneg (Nat.cast_nonneg m) i
    · obtain ⟨h1a, h1b⟩ := ih (q + 1) (by omega)
      obtain ⟨h0a, h0b⟩ := ih q (by omega)
      have hrec := coeff_rec m q
      have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
      have hq : (0:ℝ) < (q:ℝ) + 2 := by positivity
      have hS1 : S m ((q + 1) / 2) ≤ S m ((q + 2) / 2) := S_mono hm (by omega)
      have hS0 : (m:ℝ) * S m (q / 2) ≤ S m ((q + 2) / 2) := by
        have := mul_S_le hm (q / 2)
        have h' : q / 2 + 1 = (q + 2) / 2 := by omega
        rw [h'] at this; exact this
      constructor
      · have : 0 ≤ coeff (q + 2) (Dser ^ m) * (q + 2) := by
          rw [hrec]; positivity
        exact nonneg_of_mul_nonneg_left this hq
      · have : coeff (q + 2) (Dser ^ m) * ((q:ℝ) + 2) ≤ S m ((q + 2) / 2) * ((q:ℝ) + 2) := by
          rw [hrec]
          have := mul_le_mul_of_nonneg_left h0b hm
          have h1' : coeff (q + 1) (Dser ^ m) * ((q:ℝ) + 1) ≤ S m ((q + 2) / 2) * ((q:ℝ) + 1) :=
            mul_le_mul (h1b.trans hS1) le_rfl (by positivity)
              (le_trans h1a (h1b.trans hS1))
          nlinarith
        exact le_of_mul_le_mul_right this hq

end Alg

lemma gammaPDF_one_toReal (r x : ℝ) (hr : 0 < r) :
    (gammaPDF 1 r x).toReal = if 0 ≤ x then r * Real.exp (-(r * x)) else 0 := by
  rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg one_pos hr x), gammaPDFReal]
  simp only [Real.rpow_one, Real.Gamma_one, div_one, sub_self, Real.rpow_zero, mul_one]

lemma ae_ne_zero : ∀ᵐ x : ℝ, x ≠ 0 := by
  have : (volume : Measure ℝ) {0} = 0 := measure_singleton 0
  exact (measure_eq_zero_iff_ae_notMem.1 this).mono fun x hx => by simpa using hx

lemma integrable_pow_exp {r : ℝ} (hr : 0 < r) (p : ℕ) :
    Integrable (fun x : ℝ => |x| ^ p) (expMeasure r) := by
  have hpdf : Measurable (gammaPDF 1 r) := (measurable_gammaPDFReal 1 r).ennreal_ofReal
  rw [expMeasure, gammaMeasure, integrable_withDensity_iff_integrable_smul' hpdf
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (p : ℝ)) (p := 1) (b := r)
    (by have : (0:ℝ) ≤ p := Nat.cast_nonneg p
        linarith) one_pos hr
  have h2 : Integrable (Set.indicator (Ioi 0)
      (fun x : ℝ => r * (x ^ (p : ℝ) * Real.exp (-r * x ^ (1 : ℝ))))) volume :=
    (integrable_indicator_iff measurableSet_Ioi).2 (Integrable.const_mul h r)
  refine h2.congr ?_
  filter_upwards [ae_ne_zero] with x hx
  rw [gammaPDF_one_toReal r x hr, smul_eq_mul]
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · rw [indicator_of_notMem (by simpa using hneg.le), if_neg (not_le.2 hneg), zero_mul]
  · rw [indicator_of_mem (mem_Ioi.2 hpos), if_pos hpos.le, Real.rpow_natCast, Real.rpow_one,
      abs_of_pos hpos]
    ring_nf


lemma integral_pow_exp {r : ℝ} (hr : 0 < r) (j : ℕ) :
    ∫ x, x ^ j ∂(expMeasure r) = (j.factorial : ℝ) / r ^ j := by
  have hpdf : Measurable (gammaPDF 1 r) := (measurable_gammaPDFReal 1 r).ennreal_ofReal
  rw [expMeasure, gammaMeasure, integral_withDensity_eq_integral_toReal_smul hpdf
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  have h1 : ∫ x : ℝ, (gammaPDF 1 r x).toReal • x ^ j =
      ∫ x : ℝ, Set.indicator (Ioi 0)
        (fun x : ℝ => r * (x ^ (((j:ℝ) + 1) - 1) * Real.exp (-(r * x)))) x := by
    refine integral_congr_ae ?_
    filter_upwards [ae_ne_zero] with x hx
    rw [gammaPDF_one_toReal r x hr, smul_eq_mul]
    rcases lt_or_gt_of_ne hx with hneg | hpos
    · rw [indicator_of_notMem (by simpa using hneg.le), if_neg (not_le.2 hneg), zero_mul]
    · rw [indicator_of_mem (mem_Ioi.2 hpos), if_pos hpos.le, add_sub_cancel_right,
        Real.rpow_natCast]
      ring
  rw [h1, integral_indicator measurableSet_Ioi, integral_const_mul,
    Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity) hr]
  rw [Real.Gamma_nat_eq_factorial, show ((j:ℝ) + 1) = ((j + 1 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast]
  rw [one_div_pow, pow_succ]
  field_simp

lemma integrable_xpow_exp {r : ℝ} (hr : 0 < r) (j : ℕ) :
    Integrable (fun x : ℝ => x ^ j) (expMeasure r) :=
  (integrable_pow_exp hr j).mono' (continuous_pow j).aestronglyMeasurable
    (ae_of_all _ fun x => by simp [norm_pow])

lemma central_moment_exp {r : ℝ} (hr : 0 < r) (q : ℕ) :
    ∫ x, (r * x - 1) ^ q ∂(expMeasure r) = (q.factorial : ℝ) * dd q := by
  have hexp : ∀ x : ℝ, (r * x - 1) ^ q = ∑ j ∈ Finset.range (q + 1),
      (r ^ j * (-1) ^ (q - j) * (q.choose j : ℝ)) * x ^ j := by
    intro x; rw [sub_eq_add_neg, add_pow]; exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [hexp]
  rw [integral_finsetSum _ fun j _ => (integrable_xpow_exp hr j).const_mul _]
  simp_rw [integral_const_mul, integral_pow_exp hr]
  have hr0 : r ≠ 0 := hr.ne'
  have h1 : ∀ j ∈ Finset.range (q + 1), r ^ j * (-1) ^ (q - j) * (q.choose j : ℝ) *
      ((j.factorial : ℝ) / r ^ j) = (-1) ^ (q - j) * (q.choose j : ℝ) * j.factorial := by
    intro j _; field_simp
  rw [Finset.sum_congr rfl h1]
  unfold dd
  rw [Finset.mul_sum, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ q := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have e1 : q + 1 - 1 - j = q - j := by omega
  have e2 : q - (q - j) = j := by omega
  rw [e1, e2, Nat.choose_symm hj']
  have hc := Nat.choose_mul_factorial_mul_factorial hj'
  have hjf : (0:ℝ) < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
  rw [← hc]
  push_cast
  field_simp

section Prob

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma memLp_g {n : ℕ} (hn : (0:ℝ) < n) {g : ℕ → Ω → ℝ}
    (hgLaw : ∀ i, HasLaw (g i) (expMeasure (n : ℝ)) P) (i k : ℕ) (hk : k ≠ 0) :
    MemLp (g i) k P := by
  have hint : Integrable (fun x : ℝ => |x| ^ k) (expMeasure n) := integrable_pow_exp hn k
  rw [← (hgLaw i).map_eq] at hint
  have h2 := (integrable_map_measure hint.aestronglyMeasurable (hgLaw i).aemeasurable).1 hint
  rw [← integrable_norm_rpow_iff (hgLaw i).aemeasurable.aestronglyMeasurable
    (by simpa using hk) (by simp)]
  refine h2.congr (ae_of_all _ fun ω => ?_)
  simp [Real.norm_eq_abs, Real.rpow_natCast]


lemma integrable_pow_of_memLp {f : Ω → ℝ} (hf : ∀ q : ℕ, q ≠ 0 → MemLp f q P) (q : ℕ) :
    Integrable (fun ω => f ω ^ q) P := by
  rcases Nat.eq_zero_or_pos q with h0 | hq
  · subst h0; simp
  · have h := (hf q hq.ne').integrable_norm_pow hq.ne'
    refine h.mono' ((hf q hq.ne').aestronglyMeasurable.pow q) (ae_of_all _ fun ω => ?_)
    simp [norm_pow]

/-- Centred, rescaled partial sums `Y_l = ∑_{i<l} (n g_i - 1)`. -/
noncomputable def Yl (g : ℕ → Ω → ℝ) (n : ℕ) (l : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range l, ((n : ℝ) * g i ω - 1)

lemma memLp_Y {n : ℕ} (hn : (0:ℝ) < n) {g : ℕ → Ω → ℝ}
    (hgLaw : ∀ i, HasLaw (g i) (expMeasure (n : ℝ)) P) (l q : ℕ) (hq : q ≠ 0) :
    MemLp (Yl g n l) q P :=
  memLp_finset_sum (Finset.range l) fun i _ =>
    ((memLp_g hn hgLaw i q hq).const_mul (n : ℝ)).sub (memLp_const 1)

lemma memLp_Xi {n : ℕ} (hn : (0:ℝ) < n) {g : ℕ → Ω → ℝ}
    (hgLaw : ∀ i, HasLaw (g i) (expMeasure (n : ℝ)) P) (i q : ℕ) (hq : q ≠ 0) :
    MemLp (fun ω => (n : ℝ) * g i ω - 1) q P :=
  ((memLp_g hn hgLaw i q hq).const_mul (n : ℝ)).sub (memLp_const 1)

lemma moment_succ {n : ℕ} (hn : (0:ℝ) < n) {g : ℕ → Ω → ℝ} (hgIndep : iIndepFun g P)
    (hgLaw : ∀ i, HasLaw (g i) (expMeasure (n : ℝ)) P) (l p : ℕ) :
    ∫ ω, (Yl g n (l + 1) ω) ^ p ∂P = ∑ j ∈ Finset.range (p + 1),
      (p.choose j : ℝ) * (∫ ω, (Yl g n l ω) ^ j ∂P) * ((p - j).factorial * dd (p - j)) := by
  set X : ℕ → Ω → ℝ := fun i ω => (n : ℝ) * g i ω - 1 with hX
  have hXind : iIndepFun X P :=
    hgIndep.comp (fun _ x => (n : ℝ) * x - 1) (fun _ => by fun_prop)
  have hXae : ∀ i, AEMeasurable (X i) P := fun i =>
    ((hgLaw i).aemeasurable.const_mul _).sub_const _
  have hind0 := hXind.indepFun_finsetSum_of_notMem₀ hXae (s := Finset.range l) (i := l) (by simp)
  have hYeq : (∑ j ∈ Finset.range l, X j) = Yl g n l := by
    funext ω; simp [Yl, X, Finset.sum_apply]
  rw [hYeq] at hind0
  have hsplit : ∀ ω, Yl g n (l + 1) ω = Yl g n l ω + X l ω := fun ω => by
    simp only [Yl, X, Finset.sum_range_succ]
  simp_rw [hsplit, add_pow]
  have hint : ∀ j ∈ Finset.range (p + 1), Integrable
      (fun ω => Yl g n l ω ^ j * X l ω ^ (p - j) * (p.choose j : ℝ)) P := by
    intro j _
    refine Integrable.mul_const ?_ _
    have hI := (hind0.comp (measurable_id.pow_const j) (measurable_id.pow_const (p - j))).integrable_mul
      (integrable_pow_of_memLp (memLp_Y hn hgLaw l) j)
      (integrable_pow_of_memLp (memLp_Xi hn hgLaw l) (p - j))
    exact hI
  rw [integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_mul_const]
  have hmul := (hind0.comp (measurable_id.pow_const j)
    (measurable_id.pow_const (p - j))).integral_fun_mul_eq_mul_integral
    (integrable_pow_of_memLp (memLp_Y hn hgLaw l) j).aestronglyMeasurable
    (integrable_pow_of_memLp (memLp_Xi hn hgLaw l) (p - j)).aestronglyMeasurable
  simp only [Function.comp, id] at hmul
  rw [hmul]
  have hXm : ∫ ω, X l ω ^ (p - j) ∂P = ((p - j).factorial : ℝ) * dd (p - j) := by
    have := (hgLaw l).integral_comp (f := fun x : ℝ => ((n : ℝ) * x - 1) ^ (p - j))
      (by fun_prop)
    simp only [Function.comp] at this
    rw [show (fun ω => X l ω ^ (p - j)) = fun ω => ((n : ℝ) * g l ω - 1) ^ (p - j) from rfl]
    rw [this, central_moment_exp hn]
  rw [hXm]
  ring

lemma series_eq {n : ℕ} (hn : (0:ℝ) < n) {g : ℕ → Ω → ℝ} (hgIndep : iIndepFun g P)
    (hgLaw : ∀ i, HasLaw (g i) (expMeasure (n : ℝ)) P) (l : ℕ) :
    PowerSeries.mk (fun p => (∫ ω, (Yl g n l ω) ^ p ∂P) / (p.factorial : ℝ)) = Dser ^ l := by
  induction l with
  | zero =>
    ext p
    rw [PowerSeries.coeff_mk, pow_zero, PowerSeries.coeff_one]
    simp only [Yl, Finset.range_zero, Finset.sum_empty]
    rcases p with _ | p
    · simp
    · simp
  | succ l ih =>
    rw [pow_succ, ← ih]
    ext p
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i (PowerSeries.mk fun p =>
          (∫ ω, (Yl g n l ω) ^ p ∂P) / (p.factorial : ℝ)) * PowerSeries.coeff j Dser)]
    simp only [PowerSeries.coeff_mk, Dser]
    rw [moment_succ hn hgIndep hgLaw, Finset.sum_div]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j ≤ p := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hc := Nat.choose_mul_factorial_mul_factorial hj'
    have h1 : (0:ℝ) < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
    have h2 : (0:ℝ) < ((p - j).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have h3 : (0:ℝ) < (p.choose j : ℝ) := by exact_mod_cast Nat.choose_pos hj'
    rw [← hc]
    push_cast
    field_simp

end Prob

end J1Erlang

namespace J1Erlang

lemma even_sum_le (r : ℝ) (hr : 1 ≤ r) (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), r ^ (2 * i) ≤ ∑ j ∈ Finset.range (2 * k + 1), r ^ j := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e1 : ∑ i ∈ Finset.range (k + 1 + 1), r ^ (2 * i) =
        ∑ i ∈ Finset.range (k + 1), r ^ (2 * i) + r ^ (2 * (k + 1)) := Finset.sum_range_succ _ _
    have e2 : ∑ j ∈ Finset.range (2 * (k + 1) + 1), r ^ j =
        ∑ j ∈ Finset.range (2 * k + 1), r ^ j + r ^ (2 * k + 1) + r ^ (2 * (k + 1)) := by
      rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, Finset.sum_range_succ,
        Finset.sum_range_succ, show 2 * k + 1 + 1 = 2 * (k + 1) by ring]
    rw [e1, e2]
    have : 0 ≤ r ^ (2 * k + 1) := pow_nonneg (by linarith) _
    linarith

end J1Erlang

open InhomMJPStrong.J1 J1Erlang in
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 4 ≤ n) (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1)
    (g : ℕ → Ω → ℝ) (hgIndep : iIndepFun g P)
    (hgLaw : ∀ i, HasLaw (g i) (expMeasure (n : ℝ)) P) (k : ℕ) :
    let m := gridSize n eps
    let r := Real.sqrt (m : ℝ)
    let moment := ∫ ω, (arrival (fun i => g i ω) m - (m : ℝ) / (n : ℝ)) ^ (2 * k) ∂P
    moment ≤ ((2 * k).factorial : ℝ) * r / (n : ℝ) ^ (2 * k) *
      ((r ^ (2 * k + 1) - 1) / (r - 1)) ∧
    ((2 * k).factorial : ℝ) * r / (n : ℝ) ^ (2 * k) *
      ((r ^ (2 * k + 1) - 1) / (r - 1)) ≤
      2 * r * (2 * (k : ℝ) * r / (n : ℝ)) ^ (2 * k) := by
  intro m r moment
  have hn4 : (4:ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0:ℝ) < n := by linarith
  have hm4 : 4 ≤ m := by
    apply Nat.le_floor
    have : (n:ℝ) ^ (1:ℝ) ≤ (n:ℝ) ^ (1 + eps) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    rw [Real.rpow_one] at this
    push_cast; linarith
  have hm4r : (4:ℝ) ≤ m := by exact_mod_cast hm4
  have hr2 : 2 ≤ r := by
    show 2 ≤ Real.sqrt (m:ℝ)
    rw [show (2:ℝ) = Real.sqrt 4 by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hm4r
  have hrsq : r ^ 2 = (m:ℝ) := Real.sq_sqrt (by positivity)
  have hr1 : 0 < r - 1 := by linarith
  have hgeom : ∑ j ∈ Finset.range (2 * k + 1), r ^ j = (r ^ (2 * k + 1) - 1) / (r - 1) :=
    geom_sum_eq (by linarith) _
  have hpk : (0:ℝ) < ((2 * k).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  constructor
  · -- the moment identity
    have hmom : moment = (∫ ω, (Yl g n m ω) ^ (2 * k) ∂P) / (n:ℝ) ^ (2 * k) := by
      show ∫ ω, (arrival (fun i => g i ω) m - (m : ℝ) / (n : ℝ)) ^ (2 * k) ∂P = _
      rw [← integral_div]
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      simp only [arrival, Yl]
      rw [← div_pow]
      congr 1
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      field_simp
    have hser := congrArg (PowerSeries.coeff (2 * k)) (series_eq hnpos hgIndep hgLaw m)
    rw [PowerSeries.coeff_mk] at hser
    have hb := (coeff_bound m (2 * k)).2
    rw [← hser, show 2 * k / 2 = k by omega] at hb
    have hI : ∫ ω, (Yl g n m ω) ^ (2 * k) ∂P ≤ ((2 * k).factorial : ℝ) * S m k := by
      have := (div_le_iff₀ hpk).1 hb
      linarith
    have hS : S (m:ℝ) k ≤ r * ((r ^ (2 * k + 1) - 1) / (r - 1)) := by
      unfold S
      have h1 : ∑ i ∈ Finset.range (k + 1), (m:ℝ) ^ i = ∑ i ∈ Finset.range (k + 1), r ^ (2 * i) :=
        Finset.sum_congr rfl fun i _ => by rw [pow_mul, hrsq]
      rw [h1, ← hgeom]
      have h2 := even_sum_le r (by linarith) k
      have h3 : 0 ≤ ∑ j ∈ Finset.range (2 * k + 1), r ^ j :=
        Finset.sum_nonneg fun j _ => pow_nonneg (by linarith) j
      nlinarith
    rw [hmom]
    have hnk : (0:ℝ) < (n:ℝ) ^ (2 * k) := by positivity
    rw [div_le_iff₀ hnk]
    calc ∫ ω, (Yl g n m ω) ^ (2 * k) ∂P ≤ ((2 * k).factorial : ℝ) * S m k := hI
      _ ≤ ((2 * k).factorial : ℝ) * (r * ((r ^ (2 * k + 1) - 1) / (r - 1))) :=
          mul_le_mul_of_nonneg_left hS hpk.le
      _ = _ := by field_simp
  · -- the elementary bound
    have hq : (r ^ (2 * k + 1) - 1) / (r - 1) ≤ 2 * r ^ (2 * k) := by
      rw [div_le_iff₀ hr1, pow_succ]
      have : 0 ≤ r ^ (2 * k) := pow_nonneg (by linarith) _
      nlinarith
    have hfac : ((2 * k).factorial : ℝ) ≤ ((2 * k : ℕ) : ℝ) ^ (2 * k) := by
      exact_mod_cast Nat.factorial_le_pow (2 * k)
    have hA : 0 ≤ (r ^ (2 * k + 1) - 1) / (r - 1) := by
      rw [← hgeom]; exact Finset.sum_nonneg fun j _ => pow_nonneg (by linarith) j
    have hnk : (0:ℝ) < (n:ℝ) ^ (2 * k) := by positivity
    calc ((2 * k).factorial : ℝ) * r / (n : ℝ) ^ (2 * k) * ((r ^ (2 * k + 1) - 1) / (r - 1))
        ≤ ((2 * k : ℕ) : ℝ) ^ (2 * k) * r / (n : ℝ) ^ (2 * k) * (2 * r ^ (2 * k)) := by
          gcongr
      _ = 2 * r * (2 * (k : ℝ) * r / (n : ℝ)) ^ (2 * k) := by
          push_cast
          rw [div_pow, mul_pow, mul_pow]
          field_simp
          rw [mul_pow]
