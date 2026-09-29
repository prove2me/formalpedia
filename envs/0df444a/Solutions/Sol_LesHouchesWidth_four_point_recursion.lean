-- Prove2me | solution 1 for LesHouchesWidth.four_point_recursion
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T19:06:45.239226+00:00
-- url     : https://prove2.me/submissions/774550d4-d91b-4fa5-82aa-8ad408975fa1

import Mathlib
import Definitions.Def_LesHouchesWidth_GaussianMLP
import Definitions.Def_LesHouchesWidth_FiniteWidth

/-! 32a26244 LesHouchesWidth.four_point_recursion (Les Houches II, Theorem 4.2, first part).
Route: kappa4 at layer m+1 is the variance of the collective variable S_m (conditional Gaussian
layer). The laws of S_m form a Markov chain whose one-step centred moments are computed exactly
(mean, second, third moment) or bounded (even moments, Marcinkiewicz-Zygmund). An induction on the
layer, using global Taylor expansions of s -> <sigma^2>_s and of gaussVarSq with polynomial tails,
bounds all weighted centred moments uniformly in the widths; the variance recursion follows. -/

/-! Library for 32a26244 `LesHouchesWidth.four_point_recursion` (Les Houches II, Thm 4.2).
Everything in this file is CHECKED (LEANCHECK OK). Plan: PLAN.md; API notes: NOTES.md.
Done so far: M0 (Gaussian 2nd/4th moments), M1 (density derivative in the variance, derivative
formula for `gaussAvg`, `C^m` smoothness on `(0,∞)`, local 2nd-order Taylor), M2a (layer-block
reindexing, `mlpZ` locality, measure-preserving split of the parameters). -/

set_option autoImplicit false

namespace LesHouchesWidth
namespace FW

open MeasureTheory ProbabilityTheory

section gaussMoments

lemma gauss_mom2 (v : NNReal) : ∫ x, x ^ 2 ∂(gaussianReal 0 v) = v := by
  have hv := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_of_integral_eq_zero (by fun_prop) (by simp [integral_id_gaussianReal])] at hv
  exact hv

lemma hasDerivAt_expq (c t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (c * t ^ 2 / 2)) (c * t * Real.exp (c * t ^ 2 / 2)) t := by
  have := (((hasDerivAt_pow 2 t).const_mul c).div_const 2).exp
  convert this using 1; push_cast; ring

lemma gauss_mom4 (v : NNReal) : ∫ x, x ^ 4 ∂(gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet id (gaussianReal 0 v)) := by
    simp [integrableExpSet_id_gaussianReal]
  have h := iteratedDeriv_mgf_zero h0 4
  rw [mgf_id_gaussianReal] at h
  set c : ℝ := (v : ℝ) with hc
  have e : (fun t : ℝ => Real.exp (0 * t + c * t ^ 2 / 2)) = fun t => Real.exp (c * t ^ 2 / 2) := by
    funext t; simp
  rw [e] at h
  have d1 : deriv (fun t : ℝ => Real.exp (c * t ^ 2 / 2)) = fun t => c * t * Real.exp (c * t ^ 2 / 2) := by
    funext t; exact (hasDerivAt_expq c t).deriv
  have d2 : deriv (fun t : ℝ => c * t * Real.exp (c * t ^ 2 / 2)) =
      fun t => (c + c ^ 2 * t ^ 2) * Real.exp (c * t ^ 2 / 2) := by
    funext t
    have hd : HasDerivAt (fun t : ℝ => c * t * Real.exp (c * t ^ 2 / 2))
        ((c + c ^ 2 * t ^ 2) * Real.exp (c * t ^ 2 / 2)) t := by
      have := ((hasDerivAt_id t).const_mul c).mul (hasDerivAt_expq c t)
      exact this.congr_deriv (by simp only [id, mul_one]; ring)
    exact hd.deriv
  have d3 : deriv (fun t : ℝ => (c + c ^ 2 * t ^ 2) * Real.exp (c * t ^ 2 / 2)) =
      fun t => (3 * c ^ 2 * t + c ^ 3 * t ^ 3) * Real.exp (c * t ^ 2 / 2) := by
    funext t
    have hd : HasDerivAt (fun t : ℝ => (c + c ^ 2 * t ^ 2) * Real.exp (c * t ^ 2 / 2))
        ((3 * c ^ 2 * t + c ^ 3 * t ^ 3) * Real.exp (c * t ^ 2 / 2)) t := by
      have := (((hasDerivAt_pow 2 t).const_mul (c ^ 2)).const_add c).mul (hasDerivAt_expq c t)
      exact this.congr_deriv (by push_cast; ring)
    exact hd.deriv
  have d4 : deriv (fun t : ℝ => (3 * c ^ 2 * t + c ^ 3 * t ^ 3) * Real.exp (c * t ^ 2 / 2)) =
      fun t => (3 * c ^ 2 + 6 * c ^ 3 * t ^ 2 + c ^ 4 * t ^ 4) * Real.exp (c * t ^ 2 / 2) := by
    funext t
    have hd : HasDerivAt (fun t : ℝ => (3 * c ^ 2 * t + c ^ 3 * t ^ 3) * Real.exp (c * t ^ 2 / 2))
        ((3 * c ^ 2 + 6 * c ^ 3 * t ^ 2 + c ^ 4 * t ^ 4) * Real.exp (c * t ^ 2 / 2)) t := by
      have := (((hasDerivAt_id t).const_mul (3 * c ^ 2)).add
        ((hasDerivAt_pow 3 t).const_mul (c ^ 3))).mul (hasDerivAt_expq c t)
      exact this.congr_deriv (by simp only [id, Pi.add_apply]; push_cast; ring)
    exact hd.deriv
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, d1, d2, d3, d4] at h
  rw [show (∫ x, x ^ 4 ∂(gaussianReal 0 v)) = ∫ x, (id ^ 4) x ∂(gaussianReal 0 v) from rfl, ← h]
  simp

end gaussMoments

section analytic

/-- centered Gaussian density with variance `s`, as a function of `(s, t)`. -/
noncomputable def gpdf (s t : ℝ) : ℝ := (Real.sqrt (2 * Real.pi * s))⁻¹ * Real.exp (-t ^ 2 / (2 * s))

lemma gpdf_nonneg (s t : ℝ) : 0 ≤ gpdf s t := by unfold gpdf; positivity

lemma gaussAvg_eq_gpdf {s : ℝ} (hs : 0 < s) (f : ℝ → ℝ) :
    gaussAvg s f = ∫ t, gpdf s t * f t := by
  unfold gaussAvg
  rw [integral_gaussianReal_eq_integral_smul (by simpa using hs)]
  simp [gaussianPDFReal_def, gpdf, Real.coe_toNNReal _ hs.le]

lemma hasDerivAt_gpdf (t : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun s => gpdf s t) (gpdf s t * (t ^ 2 / (2 * s ^ 2) - 1 / (2 * s))) s := by
  have hpos : 0 < 2 * Real.pi * s := by positivity
  have h1 : HasDerivAt (fun s => Real.sqrt (2 * Real.pi * s))
      (2 * Real.pi / (2 * Real.sqrt (2 * Real.pi * s))) s := by
    have := ((hasDerivAt_id s).const_mul (2 * Real.pi)).sqrt hpos.ne'
    simpa using this
  have hsq : Real.sqrt (2 * Real.pi * s) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  have h2 := h1.inv hsq
  have h3 : HasDerivAt (fun s => -t ^ 2 / (2 * s)) (t ^ 2 / (2 * s ^ 2)) s := by
    have e : (fun s : ℝ => -t ^ 2 / (2 * s)) = fun s => (-t ^ 2 / 2) * s⁻¹ := by
      funext x; ring
    rw [e]
    refine ((hasDerivAt_inv hs.ne').const_mul (-t ^ 2 / 2)).congr_deriv ?_
    field_simp
  have h4 := h2.mul h3.exp
  unfold gpdf
  refine h4.congr_deriv ?_
  have hss : Real.sqrt (2 * Real.pi * s) ^ 2 = 2 * Real.pi * s := Real.sq_sqrt hpos.le
  simp only [Pi.inv_apply]
  field_simp
  rw [hss]
  ring

lemma gpdf_le {s0 s : ℝ} (hs0 : 0 < s0) (hs : s ∈ Set.Ioo (s0 / 2) (2 * s0)) (t : ℝ) :
    gpdf s t ≤ (Real.sqrt (Real.pi * s0))⁻¹ * Real.exp (-(1 / (4 * s0)) * t ^ 2) := by
  obtain ⟨h1, h2⟩ := hs
  have hspos : 0 < s := by linarith
  unfold gpdf
  apply mul_le_mul _ _ (by positivity) (by positivity)
  · apply inv_anti₀ (by positivity)
    apply Real.sqrt_le_sqrt
    nlinarith [Real.pi_pos]
  · apply Real.exp_le_exp.2
    rw [neg_div, neg_mul, neg_le_neg_iff, le_div_iff₀ (by positivity)]
    have ht : 0 ≤ t ^ 2 := sq_nonneg t
    have : 1 / (4 * s0) * t ^ 2 * (2 * s) ≤ t ^ 2 := by
      rw [show 1 / (4 * s0) * t ^ 2 * (2 * s) = t ^ 2 * (s / (2 * s0)) by field_simp; ring]
      have : s / (2 * s0) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      nlinarith
    linarith

lemma factor_le {s0 s : ℝ} (hs0 : 0 < s0) (hs : s ∈ Set.Ioo (s0 / 2) (2 * s0)) (t : ℝ) :
    |t ^ 2 / (2 * s ^ 2) - 1 / (2 * s)| ≤ (2 / s0 ^ 2 + 1 / s0) * (1 + |t|) ^ 2 := by
  obtain ⟨h1, _⟩ := hs
  have hspos : 0 < s := by linarith
  have ha : 0 ≤ t ^ 2 / (2 * s ^ 2) := by positivity
  have hb : 0 ≤ 1 / (2 * s) := by positivity
  have hA : t ^ 2 / (2 * s ^ 2) ≤ 2 / s0 ^ 2 * t ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : s0 ^ 2 ≤ 4 * s ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_left this (sq_nonneg t)
    rw [show 2 / s0 ^ 2 * t ^ 2 * (2 * s ^ 2) = t ^ 2 * (4 * s ^ 2) / s0 ^ 2 by ring,
      le_div_iff₀ (by positivity)]
    linarith
  have hB : 1 / (2 * s) ≤ 1 / s0 := by
    apply one_div_le_one_div_of_le hs0; linarith
  have ht : t ^ 2 ≤ (1 + |t|) ^ 2 := by
    rw [← sq_abs t]; nlinarith [abs_nonneg t]
  have h1' : (1 : ℝ) ≤ (1 + |t|) ^ 2 := by nlinarith [abs_nonneg t]
  calc |t ^ 2 / (2 * s ^ 2) - 1 / (2 * s)| ≤ t ^ 2 / (2 * s ^ 2) + 1 / (2 * s) := by
        rw [abs_le]; constructor <;> linarith
    _ ≤ 2 / s0 ^ 2 * (1 + |t|) ^ 2 + 1 / s0 * (1 + |t|) ^ 2 := by
        have := mul_le_mul_of_nonneg_left ht (by positivity : (0:ℝ) ≤ 2 / s0 ^ 2)
        have := mul_le_mul_of_nonneg_left h1' (by positivity : (0:ℝ) ≤ 1 / s0)
        linarith
    _ = (2 / s0 ^ 2 + 1 / s0) * (1 + |t|) ^ 2 := by ring

lemma integrable_one_add_abs_pow_mul_exp {b : ℝ} (hb : 0 < b) (k : ℕ) :
    Integrable (fun x : ℝ => (1 + |x|) ^ k * Real.exp (-b * x ^ 2)) := by
  have h : ∀ x : ℝ, (1 + |x|) ^ k * Real.exp (-b * x ^ 2) =
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * (|x| ^ j * Real.exp (-b * x ^ 2)) := by
    intro x
    rw [add_comm, add_pow, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro j _; simp only [one_pow, mul_one]; ring
  simp_rw [h]
  apply integrable_finsetSum
  intro j _
  apply Integrable.const_mul
  have := (integrable_rpow_mul_exp_neg_mul_sq hb (s := (j : ℝ))
    (by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith)).norm
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [Real.norm_eq_abs, Real.rpow_natCast, abs_of_pos (Real.exp_pos _)]

lemma measurable_gpdf : Measurable (Function.uncurry gpdf) := by
  unfold gpdf; fun_prop

theorem hasDerivAt_gaussInt {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ} {k : ℕ}
    (hfb : ∀ t, |f t| ≤ C * (1 + |t|) ^ k) {s0 : ℝ} (hs0 : 0 < s0) :
    HasDerivAt (fun s => ∫ t, gpdf s t * f t)
      (∫ t, gpdf s0 t * (t ^ 2 / (2 * s0 ^ 2) - 1 / (2 * s0)) * f t) s0 := by
  have hmeas : ∀ s, Measurable (fun t => gpdf s t) := fun s => by unfold gpdf; fun_prop
  have hs : Set.Ioo (s0 / 2) (2 * s0) ∈ nhds s0 := Ioo_mem_nhds (by linarith) (by linarith)
  have hb : 0 < 1 / (4 * s0) := by positivity
  set B : ℝ := (Real.sqrt (Real.pi * s0))⁻¹ * (2 / s0 ^ 2 + 1 / s0) * C
  have hbound : ∀ t, ∀ s ∈ Set.Ioo (s0 / 2) (2 * s0),
      ‖gpdf s t * (t ^ 2 / (2 * s ^ 2) - 1 / (2 * s)) * f t‖ ≤
        B * ((1 + |t|) ^ (k + 2) * Real.exp (-(1 / (4 * s0)) * t ^ 2)) := by
    intro t s hs'
    have hC : 0 ≤ C := (abs_nonneg _).trans (by simpa using hfb 0)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (gpdf_nonneg s t)]
    have e1 := gpdf_le hs0 hs' t
    have e2 := factor_le hs0 hs' t
    have e3 := hfb t
    calc gpdf s t * |t ^ 2 / (2 * s ^ 2) - 1 / (2 * s)| * |f t|
        ≤ ((Real.sqrt (Real.pi * s0))⁻¹ * Real.exp (-(1 / (4 * s0)) * t ^ 2)) *
          ((2 / s0 ^ 2 + 1 / s0) * (1 + |t|) ^ 2) * (C * (1 + |t|) ^ k) := by
          gcongr
      _ = B * ((1 + |t|) ^ (k + 2) * Real.exp (-(1 / (4 * s0)) * t ^ 2)) := by
          simp only [B]; ring
  have hint : Integrable (fun t => B * ((1 + |t|) ^ (k + 2) * Real.exp (-(1 / (4 * s0)) * t ^ 2))) :=
    (integrable_one_add_abs_pow_mul_exp hb (k + 2)).const_mul B
  have hF_int : Integrable (fun t => gpdf s0 t * f t) := by
    refine Integrable.mono' ((integrable_one_add_abs_pow_mul_exp hb k).const_mul
      ((Real.sqrt (Real.pi * s0))⁻¹ * C)) ((hmeas s0).mul hf).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    have hC : 0 ≤ C := (abs_nonneg _).trans (by simpa using hfb 0)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gpdf_nonneg s0 t)]
    have e1 := gpdf_le (s := s0) hs0 ⟨by linarith, by linarith⟩ t
    calc gpdf s0 t * |f t| ≤ ((Real.sqrt (Real.pi * s0))⁻¹ * Real.exp (-(1 / (4 * s0)) * t ^ 2)) *
          (C * (1 + |t|) ^ k) := by gcongr; exact hfb t
      _ = _ := by ring
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := s0)
    (F := fun s t => gpdf s t * f t)
    (F' := fun s t => gpdf s t * (t ^ 2 / (2 * s ^ 2) - 1 / (2 * s)) * f t) hs
    (Filter.Eventually.of_forall fun s => ((hmeas s).mul hf).aestronglyMeasurable) hF_int
    (((hmeas s0).mul (by fun_prop)).mul hf).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t s hs' => hbound t s hs') hint
    (Filter.Eventually.of_forall fun t s hs' => by
      have hsp : 0 < s := by linarith [hs'.1]
      exact (hasDerivAt_gpdf t hsp).mul_const (f t))
  exact this.2

/-- polynomially bounded measurable functions, with the bound in the form `C (1 + |t|)^k`. -/
def PB (f : ℝ → ℝ) : Prop := Measurable f ∧ ∃ C : ℝ, ∃ k : ℕ, ∀ t, |f t| ≤ C * (1 + |t|) ^ k

lemma PB.sq_mul {f : ℝ → ℝ} (hf : PB f) : PB (fun t => t ^ 2 * f t) := by
  obtain ⟨hm, C, k, hC⟩ := hf
  refine ⟨(measurable_id.pow_const 2).mul hm, C, k + 2, fun t => ?_⟩
  rw [abs_mul, abs_pow]
  have h1 : |t| ^ 2 ≤ (1 + |t|) ^ 2 := by
    apply pow_le_pow_left₀ (abs_nonneg t); linarith
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (by simpa using hC 0)
  calc |t| ^ 2 * |f t| ≤ (1 + |t|) ^ 2 * (C * (1 + |t|) ^ k) :=
        mul_le_mul h1 (hC t) (abs_nonneg _) (by positivity)
    _ = C * (1 + |t|) ^ (k + 2) := by ring

lemma integrable_gpdf_mul {f : ℝ → ℝ} (hf : PB f) {s0 : ℝ} (hs0 : 0 < s0) :
    Integrable (fun t => gpdf s0 t * f t) := by
  obtain ⟨hm, C, k, hfb⟩ := hf
  have hb : 0 < 1 / (4 * s0) := by positivity
  have hmeas : Measurable (fun t => gpdf s0 t) := by unfold gpdf; fun_prop
  refine Integrable.mono' ((integrable_one_add_abs_pow_mul_exp hb k).const_mul
    ((Real.sqrt (Real.pi * s0))⁻¹ * C)) (hmeas.mul hm).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  have hC : 0 ≤ C := (abs_nonneg _).trans (by simpa using hfb 0)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gpdf_nonneg s0 t)]
  have e1 := gpdf_le (s := s0) hs0 ⟨by linarith, by linarith⟩ t
  calc gpdf s0 t * |f t| ≤ ((Real.sqrt (Real.pi * s0))⁻¹ * Real.exp (-(1 / (4 * s0)) * t ^ 2)) *
        (C * (1 + |t|) ^ k) := by gcongr; exact hfb t
    _ = _ := by ring

theorem hasDerivAt_gaussAvg {f : ℝ → ℝ} (hf : PB f) {s0 : ℝ} (hs0 : 0 < s0) :
    HasDerivAt (fun s => gaussAvg s f)
      ((gaussAvg s0 (fun t => t ^ 2 * f t) - s0 * gaussAvg s0 f) / (2 * s0 ^ 2)) s0 := by
  obtain ⟨hm, C, k, hfb⟩ := hf
  have h := hasDerivAt_gaussInt hm hfb hs0
  have hev : (fun s => gaussAvg s f) =ᶠ[nhds s0] (fun s => ∫ t, gpdf s t * f t) := by
    filter_upwards [Ioi_mem_nhds hs0] with s hs
    exact gaussAvg_eq_gpdf hs f
  refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [gaussAvg_eq_gpdf hs0, gaussAvg_eq_gpdf hs0]
  have i1 := integrable_gpdf_mul (PB.sq_mul ⟨hm, C, k, hfb⟩) hs0
  have i2 := integrable_gpdf_mul ⟨hm, C, k, hfb⟩ hs0
  have e : (fun t => gpdf s0 t * (t ^ 2 / (2 * s0 ^ 2) - 1 / (2 * s0)) * f t) =
      fun t => (1 / (2 * s0 ^ 2)) * (gpdf s0 t * (t ^ 2 * f t)) - (1 / (2 * s0)) * (gpdf s0 t * f t) := by
    funext t; ring
  rw [e, integral_sub (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul]
  field_simp

theorem contDiffOn_gaussAvg : ∀ (m : ℕ) {f : ℝ → ℝ}, PB f →
    ContDiffOn ℝ m (fun s => gaussAvg s f) (Set.Ioi 0)
  | 0, f, hf => by
    simp only [CharP.cast_eq_zero, contDiffOn_zero]
    exact fun s hs => (hasDerivAt_gaussAvg hf hs).continuousAt.continuousWithinAt
  | m + 1, f, hf => by
    rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun s hs => (hasDerivAt_gaussAvg hf hs).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    have h1 := contDiffOn_gaussAvg m (PB.sq_mul hf)
    have h2 := contDiffOn_gaussAvg m hf
    have h3 : ContDiffOn ℝ m (fun s => (gaussAvg s (fun t => t ^ 2 * f t) - s * gaussAvg s f) /
        (2 * s ^ 2)) (Set.Ioi 0) :=
      (h1.sub (contDiffOn_id.mul h2)).div (contDiffOn_const.mul (contDiffOn_id.pow 2))
        (fun s hs => by have : (0:ℝ) < s := hs; positivity)
    refine h3.congr fun s hs => ?_
    exact (hasDerivAt_gaussAvg hf hs).deriv

theorem local_taylor2 {g : ℝ → ℝ} {K : ℝ} (hK : 0 < K) (hg : ContDiffOn ℝ 3 g (Set.Ioi 0)) :
    ∃ c2 M ε : ℝ, 0 < ε ∧ ∀ s, |s - K| < ε →
      |g s - g K - deriv g K * (s - K) - c2 * (s - K) ^ 2| ≤ M * |s - K| ^ 3 := by
  have ho := taylor_isLittleO (convex_Ioi 0) hK hg
  rw [isOpen_Ioi.nhdsWithin_eq hK] at ho
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (ho.bound one_pos)
  set d3 := iteratedDerivWithin 3 g (Set.Ioi 0) K
  refine ⟨iteratedDerivWithin 2 g (Set.Ioi 0) K / 2, 1 + |d3| / 6, ε, hε, fun s hs => ?_⟩
  have h := hball (show dist s K < ε by rwa [Real.dist_eq])
  rw [taylor_within_apply] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, iteratedDerivWithin_zero,
    iteratedDerivWithin_one, derivWithin_of_isOpen isOpen_Ioi (show K ∈ Set.Ioi 0 from hK), Real.norm_eq_abs,
    smul_eq_mul, one_mul, zero_add, abs_pow] at h
  have e : g s - g K - deriv g K * (s - K) - iteratedDerivWithin 2 g (Set.Ioi 0) K / 2 * (s - K) ^ 2 =
      (g s - (((Nat.factorial 0 : ℝ))⁻¹ * (s - K) ^ 0 * g K +
        ((Nat.factorial 1 : ℝ))⁻¹ * (s - K) ^ 1 * deriv g K +
        ((Nat.factorial 2 : ℝ))⁻¹ * (s - K) ^ 2 * iteratedDerivWithin 2 g (Set.Ioi 0) K +
        ((Nat.factorial 3 : ℝ))⁻¹ * (s - K) ^ 3 * d3)) + d3 / 6 * (s - K) ^ 3 := by
    simp [Nat.factorial]; ring
  rw [e]
  calc _ ≤ |g s - (((Nat.factorial 0 : ℝ))⁻¹ * (s - K) ^ 0 * g K +
        ((Nat.factorial 1 : ℝ))⁻¹ * (s - K) ^ 1 * deriv g K +
        ((Nat.factorial 2 : ℝ))⁻¹ * (s - K) ^ 2 * iteratedDerivWithin 2 g (Set.Ioi 0) K +
        ((Nat.factorial 3 : ℝ))⁻¹ * (s - K) ^ 3 * d3)| + |d3 / 6 * (s - K) ^ 3| := abs_add_le _ _
    _ ≤ |s - K| ^ 3 + |d3| / 6 * |s - K| ^ 3 := by
        refine add_le_add h (le_of_eq ?_)
        rw [abs_mul, abs_div, abs_pow]; norm_num
    _ = _ := by ring


end analytic

section split

variable {n : ℕ → ℕ} {L : ℕ}

/-- the layer a parameter belongs to (`ℓ` for `b^{(ℓ+1)}` and `W^{(ℓ+1)}`). -/
def layerOf : ParamIndex n L → ℕ
  | .inl a => a.1.val
  | .inr a => a.1.val

/-- the activation fed into layer `m + 1`. -/
noncomputable def act (Cb CW : ℝ) (σ : ℝ → ℝ) (θ : Params n L) (x : Fin (n 0) → ℝ) (m : ℕ)
    (j : Fin (n m)) : ℝ :=
  if m = 0 then mlpZ Cb CW σ θ x m j else σ (mlpZ Cb CW σ θ x m j)

lemma mlpZ_succ (Cb CW : ℝ) (σ : ℝ → ℝ) (θ : Params n L) (x : Fin (n 0) → ℝ) (m : ℕ)
    (i : Fin (n (m + 1))) :
    mlpZ Cb CW σ θ x (m + 1) i = mlpBias Cb θ m i + ∑ j, mlpWeight CW θ m i j * act Cb CW σ θ x m j :=
  rfl

lemma mlpZ_congr (Cb CW : ℝ) (σ : ℝ → ℝ) {θ θ' : Params n L} (x : Fin (n 0) → ℝ) :
    ∀ m : ℕ, (∀ a : ParamIndex n L, layerOf a < m → θ a = θ' a) →
      mlpZ Cb CW σ θ x m = mlpZ Cb CW σ θ' x m
  | 0, _ => rfl
  | m + 1, h => by
    have ih := mlpZ_congr Cb CW σ x m (fun a ha => h a (by omega))
    funext i
    rw [mlpZ_succ, mlpZ_succ]
    have hb : mlpBias Cb θ m i = mlpBias Cb θ' m i := by
      unfold mlpBias; split_ifs with hl
      · rw [h _ (by simp [layerOf])]
      · rfl
    have hw : ∀ j, mlpWeight CW θ m i j = mlpWeight CW θ' m i j := by
      intro j; unfold mlpWeight; split_ifs with hl
      · rw [h _ (by simp [layerOf])]
      · rfl
    rw [hb]
    refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
    rw [hw, act, act, ih]

/-- the block of layer-`m` parameters, indexed by (output unit, bias or input unit). -/
def blk (m : ℕ) (hm : m < L + 1) : Fin (n (m + 1)) × Option (Fin (n m)) → ParamIndex n L
  | (i, none) => .inl ⟨⟨m, hm⟩, i⟩
  | (i, some j) => .inr ⟨⟨m, hm⟩, (i, j)⟩

lemma layerOf_blk (m : ℕ) (hm : m < L + 1) (p : Fin (n (m + 1)) × Option (Fin (n m))) :
    layerOf (blk m hm p) = m := by
  rcases p with ⟨i, _ | j⟩ <;> rfl

lemma blk_injective (m : ℕ) (hm : m < L + 1) : Function.Injective (blk (n := n) m hm) := by
  rintro ⟨i, _ | j⟩ ⟨i', _ | j'⟩ h <;> simp_all [blk]

lemma blk_surj (m : ℕ) (hm : m < L + 1) (a : ParamIndex n L) (ha : layerOf a = m) :
    ∃ p, blk m hm p = a := by
  rcases a with ⟨⟨ℓ, hl⟩, i⟩ | ⟨⟨ℓ, hl⟩, i, j⟩
  · simp only [layerOf] at ha; subst ha; exact ⟨(i, none), rfl⟩
  · simp only [layerOf] at ha; subst ha; exact ⟨(i, some j), rfl⟩

/-- `blk` as an equivalence onto the layer-`m` parameters. -/
noncomputable def blkEquiv (m : ℕ) (hm : m < L + 1) :
    Fin (n (m + 1)) × Option (Fin (n m)) ≃ {a : ParamIndex n L // layerOf a = m} :=
  Equiv.ofBijective (fun p => ⟨blk m hm p, layerOf_blk m hm p⟩)
    ⟨fun p q h => blk_injective m hm (congrArg Subtype.val h),
     fun a => by
      obtain ⟨p, hp⟩ := blk_surj m hm a.1 a.2
      exact ⟨p, Subtype.ext hp⟩⟩

/-- the full reindexing: layer-`m` block ⊕ everything else. -/
noncomputable def splitEquiv (m : ℕ) (hm : m < L + 1) :
    (Fin (n (m + 1)) × Option (Fin (n m))) ⊕ {a : ParamIndex n L // ¬ layerOf a = m} ≃
      ParamIndex n L :=
  (Equiv.sumCongr (blkEquiv m hm) (Equiv.refl _)).trans (Equiv.sumCompl _)

/-- measurable reindexing `Params ≃ (layer-m block, curried) × (the rest)`. -/
noncomputable def splitME (m : ℕ) (hm : m < L + 1) :
    Params n L ≃ᵐ (Fin (n (m + 1)) → Option (Fin (n m)) → ℝ) ×
      ({a : ParamIndex n L // ¬ layerOf a = m} → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (splitEquiv m hm)).symm.trans
    ((MeasurableEquiv.sumPiEquivProdPi fun _ => ℝ).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.curry _ _ ℝ) (MeasurableEquiv.refl _)))

lemma splitME_apply (m : ℕ) (hm : m < L + 1) (θ : Params n L) :
    splitME m hm θ = (fun i q => θ (blk m hm (i, q)), fun b => θ b.1) := by
  ext i q <;> rfl

lemma mp_curry {A B : Type*} [Fintype A] [Fintype B] (g : Measure ℝ) [IsProbabilityMeasure g] :
    MeasurePreserving (MeasurableEquiv.curry A B ℝ) (Measure.pi fun _ : A × B => g)
      (Measure.pi fun _ : A => Measure.pi fun _ : B => g) := by
  refine ⟨(MeasurableEquiv.curry A B ℝ).measurable, ?_⟩
  have := Measure.infinitePi_map_curry (ι := A) (κ := B) (X := ℝ) (fun _ _ => g)
  simp only [Measure.infinitePi_eq_pi] at this
  exact this

lemma measurePreserving_splitME (m : ℕ) (hm : m < L + 1) :
    MeasurePreserving (splitME m hm) (stdGaussianParams n L)
      ((Measure.pi fun _ : Fin (n (m + 1)) => Measure.pi fun _ : Option (Fin (n m)) =>
          gaussianReal 0 1).prod
        (Measure.pi fun _ : {a : ParamIndex n L // ¬ layerOf a = m} => gaussianReal 0 1)) := by
  have h1 := (measurePreserving_piCongrLeft (fun _ : ParamIndex n L => gaussianReal 0 1)
    (splitEquiv m hm)).symm
  have h2 := measurePreserving_sumPiEquivProdPi
    (fun _ : (Fin (n (m + 1)) × Option (Fin (n m))) ⊕ {a : ParamIndex n L // ¬ layerOf a = m} =>
      gaussianReal 0 1)
  have h3 := (mp_curry (A := Fin (n (m + 1))) (B := Option (Fin (n m))) (gaussianReal 0 1)).prod
    (MeasurePreserving.id (Measure.pi fun _ : {a : ParamIndex n L // ¬ layerOf a = m} =>
      gaussianReal 0 1))
  exact h3.comp (h2.comp h1)


end split

section growth

lemma PB.const (c : ℝ) : PB (fun _ => c) :=
  ⟨measurable_const, |c|, 0, fun t => by simp⟩

lemma PB.id' : PB (fun t => t) :=
  ⟨measurable_id, 1, 1, fun t => by simp⟩

lemma PB.nonneg_const {f : ℝ → ℝ} {C : ℝ} {k : ℕ} (h : ∀ t, |f t| ≤ C * (1 + |t|) ^ k) : 0 ≤ C :=
  (abs_nonneg _).trans (by simpa using h 0)

lemma PB.mul {f g : ℝ → ℝ} (hf : PB f) (hg : PB g) : PB (fun t => f t * g t) := by
  obtain ⟨hfm, C1, k1, h1⟩ := hf
  obtain ⟨hgm, C2, k2, h2⟩ := hg
  refine ⟨hfm.mul hgm, C1 * C2, k1 + k2, fun t => ?_⟩
  rw [abs_mul, pow_add]
  have := PB.nonneg_const h1
  calc |f t| * |g t| ≤ (C1 * (1 + |t|) ^ k1) * (C2 * (1 + |t|) ^ k2) :=
        mul_le_mul (h1 t) (h2 t) (abs_nonneg _) (by positivity)
    _ = _ := by ring

lemma PB.add {f g : ℝ → ℝ} (hf : PB f) (hg : PB g) : PB (fun t => f t + g t) := by
  obtain ⟨hfm, C1, k1, h1⟩ := hf
  obtain ⟨hgm, C2, k2, h2⟩ := hg
  refine ⟨hfm.add hgm, C1 + C2, k1 + k2, fun t => ?_⟩
  have c1 := PB.nonneg_const h1
  have c2 := PB.nonneg_const h2
  have e1 : (1 + |t|) ^ k1 ≤ (1 + |t|) ^ (k1 + k2) :=
    pow_le_pow_right₀ (by linarith [abs_nonneg t]) (by omega)
  have e2 : (1 + |t|) ^ k2 ≤ (1 + |t|) ^ (k1 + k2) :=
    pow_le_pow_right₀ (by linarith [abs_nonneg t]) (by omega)
  calc |f t + g t| ≤ |f t| + |g t| := abs_add_le _ _
    _ ≤ C1 * (1 + |t|) ^ k1 + C2 * (1 + |t|) ^ k2 := add_le_add (h1 t) (h2 t)
    _ ≤ C1 * (1 + |t|) ^ (k1 + k2) + C2 * (1 + |t|) ^ (k1 + k2) := by gcongr
    _ = _ := by ring

lemma PB.const_mul {f : ℝ → ℝ} (hf : PB f) (c : ℝ) : PB (fun t => c * f t) :=
  (PB.const c).mul hf

lemma PB.sub {f g : ℝ → ℝ} (hf : PB f) (hg : PB g) : PB (fun t => f t - g t) := by
  have := hf.add (hg.const_mul (-1))
  refine ⟨by simpa [sub_eq_add_neg] using this.1, ?_⟩
  obtain ⟨_, C, k, h⟩ := this
  exact ⟨C, k, fun t => by simpa [sub_eq_add_neg] using h t⟩

lemma PB.pow {f : ℝ → ℝ} (hf : PB f) : ∀ j : ℕ, PB (fun t => f t ^ j)
  | 0 => by simpa using PB.const 1
  | j + 1 => by simpa [pow_succ] using (PB.pow hf j).mul hf

lemma PB.of_polyBounded {σ : ℝ → ℝ} (hm : Measurable σ) (hp : PolyBounded σ) : PB σ := by
  obtain ⟨C, k, h⟩ := hp
  have hC : 0 ≤ C := by
    have h0 := h 0
    have : 0 ≤ C * (1 + |(0:ℝ)| ^ k) := (abs_nonneg _).trans h0
    have h1 : 0 < 1 + |(0:ℝ)| ^ k := by positivity
    exact nonneg_of_mul_nonneg_left this h1
  refine ⟨hm, 2 * C, k, fun t => ?_⟩
  have a1 : (1 : ℝ) ≤ (1 + |t|) ^ k := one_le_pow₀ (by linarith [abs_nonneg t])
  have a2 : |t| ^ k ≤ (1 + |t|) ^ k := pow_le_pow_left₀ (abs_nonneg t) (by linarith) k
  calc |σ t| ≤ C * (1 + |t| ^ k) := h t
    _ ≤ C * (2 * (1 + |t|) ^ k) := by gcongr; linarith
    _ = _ := by ring

lemma integrable_one_add_abs_pow_gauss (v : NNReal) (k : ℕ) :
    Integrable (fun u : ℝ => (1 + |u|) ^ k) (gaussianReal 0 v) := by
  have hm : MemLp (id : ℝ → ℝ) (k : ENNReal) (gaussianReal 0 v) := by
    simpa using memLp_id_gaussianReal (μ := 0) (v := v) (k : NNReal)
  have hi := ((integrable_const (1 : ℝ)).add hm.integrable_norm_pow').const_mul (2 ^ k)
  refine hi.mono' ((continuous_const.add continuous_abs).pow k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have := add_pow_le (zero_le_one) (abs_nonneg u) k
  simp only [one_pow, id, Real.norm_eq_abs] at this ⊢
  calc (1 + |u|) ^ k ≤ 2 ^ (k - 1) * (1 + |u| ^ k) := this
    _ ≤ 2 ^ k * (1 + |u| ^ k) := by
        gcongr
        · norm_num
        · omega

lemma PB.integrable {f : ℝ → ℝ} (hf : PB f) (v : NNReal) : Integrable f (gaussianReal 0 v) := by
  obtain ⟨hm, C, k, h⟩ := hf
  exact ((integrable_one_add_abs_pow_gauss v k).const_mul C).mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact h t)

lemma gaussAvg_of_nonpos {s : ℝ} (hs : s ≤ 0) (f : ℝ → ℝ) : gaussAvg s f = f 0 := by
  unfold gaussAvg
  rw [Real.toNNReal_of_nonpos hs, gaussianReal_zero_var, integral_dirac]

lemma gaussAvg_scale {s : ℝ} (hs : 0 < s) {f : ℝ → ℝ} (hf : Measurable f) :
    gaussAvg s f = ∫ u, f (Real.sqrt s * u) ∂(gaussianReal 0 1) := by
  have hmap : (gaussianReal 0 1).map (fun u => Real.sqrt s * u) = gaussianReal 0 s.toNNReal := by
    rw [gaussianReal_map_const_mul, mul_zero]
    congr 1
    ext
    simp [Real.sq_sqrt hs.le, Real.coe_toNNReal _ hs.le]
  unfold gaussAvg
  rw [← hmap, integral_map (by fun_prop) hf.aestronglyMeasurable]

theorem PB.avg {f : ℝ → ℝ} (hf : PB f) : PB (fun s => gaussAvg s f) := by
  have hcont : ContinuousOn (fun s => gaussAvg s f) (Set.Ioi 0) :=
    fun s hs => (hasDerivAt_gaussAvg hf hs).continuousAt.continuousWithinAt
  have hmeas : Measurable (fun s => gaussAvg s f) := by
    have e : (fun s => gaussAvg s f) = (Set.Ioi (0:ℝ)).piecewise (fun s => gaussAvg s f) (fun _ => f 0) := by
      funext s
      by_cases h : s ∈ Set.Ioi (0:ℝ)
      · rw [Set.piecewise_eq_of_mem _ _ _ h]
      · rw [Set.piecewise_eq_of_notMem _ _ _ h]
        exact gaussAvg_of_nonpos (not_lt.1 h) f
    rw [e]
    exact hcont.measurable_piecewise continuousOn_const measurableSet_Ioi
  obtain ⟨hm, C, k, h⟩ := hf
  have hC := PB.nonneg_const h
  set Mk := ∫ u, (1 + |u|) ^ k ∂(gaussianReal 0 1)
  have hMk : 0 ≤ Mk := integral_nonneg fun u => by positivity
  refine ⟨hmeas, C * (Mk * 2 ^ k) + C, k, fun s => ?_⟩
  have hone : (1 : ℝ) ≤ (1 + |s|) ^ k := one_le_pow₀ (by linarith [abs_nonneg s])
  show |gaussAvg s f| ≤ _
  rcases le_or_gt s 0 with hs | hs
  · rw [gaussAvg_of_nonpos hs]
    have h0 := h 0
    simp only [abs_zero, add_zero, one_pow, mul_one] at h0
    have : 0 ≤ C * (Mk * 2 ^ k) * (1 + |s|) ^ k := by positivity
    nlinarith
  · rw [gaussAvg_scale hs hm]
    have hsq : Real.sqrt s ≤ 1 + s := by nlinarith [Real.sq_sqrt hs.le, Real.sqrt_nonneg s]
    have hbase : (1 + Real.sqrt s) ≤ 2 * (1 + |s|) := by rw [abs_of_pos hs]; linarith
    have hpt : ∀ u, |f (Real.sqrt s * u)| ≤ C * (1 + Real.sqrt s) ^ k * (1 + |u|) ^ k := by
      intro u
      have hu : 1 + |Real.sqrt s * u| ≤ (1 + Real.sqrt s) * (1 + |u|) := by
        rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg s)]
        nlinarith [Real.sqrt_nonneg s, abs_nonneg u]
      calc |f (Real.sqrt s * u)| ≤ C * (1 + |Real.sqrt s * u|) ^ k := h _
        _ ≤ C * ((1 + Real.sqrt s) * (1 + |u|)) ^ k := by gcongr
        _ = _ := by rw [mul_pow]; ring
    have hint := (integrable_one_add_abs_pow_gauss 1 k).const_mul (C * (1 + Real.sqrt s) ^ k)
    calc |∫ u, f (Real.sqrt s * u) ∂(gaussianReal 0 1)|
        ≤ ∫ u, |f (Real.sqrt s * u)| ∂(gaussianReal 0 1) := abs_integral_le_integral_abs
      _ ≤ ∫ u, C * (1 + Real.sqrt s) ^ k * (1 + |u|) ^ k ∂(gaussianReal 0 1) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => abs_nonneg _) hint
            (Filter.Eventually.of_forall hpt)
      _ = C * (1 + Real.sqrt s) ^ k * Mk := integral_const_mul _ _
      _ ≤ C * (2 * (1 + |s|)) ^ k * Mk := by gcongr
      _ = C * (Mk * 2 ^ k) * (1 + |s|) ^ k := by rw [mul_pow]; ring
      _ ≤ _ := by nlinarith

/-- from a local bound near `K` and a global polynomial bound to a global bound with polynomial tails. -/
theorem tail_of_local {F : ℝ → ℝ} {K ε M : ℝ} {a : ℕ} (hε : 0 < ε) (hF : PB F)
    (hloc : ∀ s, |s - K| < ε → |F s| ≤ M * |s - K| ^ a) :
    ∃ M' : ℝ, ∃ q : ℕ, ∀ s, |F s| ≤ M' * (|s - K| ^ a * (1 + (s - K) ^ 2) ^ q) := by
  obtain ⟨_, C, p, h⟩ := hF
  have hC := PB.nonneg_const h
  refine ⟨|M| + C * (1 + |K|) ^ p * 2 ^ p / ε ^ a, p, fun s => ?_⟩
  set d := |s - K| with hd
  have hd0 : 0 ≤ d := abs_nonneg _
  have hsq : (s - K) ^ 2 = d ^ 2 := (sq_abs _).symm
  rw [hsq]
  have hfac : (1 : ℝ) ≤ (1 + d ^ 2) ^ p := one_le_pow₀ (by nlinarith)
  have hB : 0 ≤ C * (1 + |K|) ^ p * 2 ^ p / ε ^ a := by positivity
  have hdA : 0 ≤ d ^ a * (1 + d ^ 2) ^ p := by positivity
  rcases lt_or_ge d ε with hlt | hge
  · have := hloc s hlt
    calc |F s| ≤ M * d ^ a := this
      _ ≤ |M| * d ^ a := by gcongr; exact le_abs_self M
      _ ≤ |M| * (d ^ a * (1 + d ^ 2) ^ p) := by
          gcongr; exact le_mul_of_one_le_right (by positivity) hfac
      _ ≤ _ := by nlinarith
  · have h1 : 1 + |s| ≤ (1 + |K|) * (1 + d) := by
      have : |s| ≤ |K| + d := by
        calc |s| = |K + (s - K)| := by ring_nf
          _ ≤ |K| + |s - K| := abs_add_le _ _
      nlinarith [abs_nonneg K]
    have h2 : (1 + d) ^ p ≤ 2 ^ p * (1 + d ^ 2) ^ p := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by linarith)
      nlinarith
    have h3 : (1 : ℝ) ≤ d ^ a / ε ^ a := by
      rw [le_div_iff₀ (by positivity), one_mul]
      exact pow_le_pow_left₀ hε.le hge a
    calc |F s| ≤ C * (1 + |s|) ^ p := h s
      _ ≤ C * ((1 + |K|) * (1 + d)) ^ p := by gcongr
      _ = C * (1 + |K|) ^ p * (1 + d) ^ p := by rw [mul_pow, mul_assoc]
      _ ≤ C * (1 + |K|) ^ p * (2 ^ p * (1 + d ^ 2) ^ p) := by gcongr
      _ ≤ C * (1 + |K|) ^ p * (2 ^ p * (1 + d ^ 2) ^ p) * (d ^ a / ε ^ a) :=
          le_mul_of_one_le_right (by positivity) h3
      _ = C * (1 + |K|) ^ p * 2 ^ p / ε ^ a * (d ^ a * (1 + d ^ 2) ^ p) := by
          field_simp
      _ ≤ _ := by gcongr; linarith [abs_nonneg M]

/-- global second-order Taylor expansion with cubic remainder and polynomial tails. -/
theorem taylor_global {F : ℝ → ℝ} (hF : PB F) (hc : ContDiffOn ℝ 3 F (Set.Ioi 0)) {K : ℝ}
    (hK : 0 < K) :
    ∃ c2 M : ℝ, ∃ q : ℕ, ∀ s, |F s - F K - deriv F K * (s - K) - c2 * (s - K) ^ 2| ≤
      M * (|s - K| ^ 3 * (1 + (s - K) ^ 2) ^ q) := by
  obtain ⟨c2, M, ε, hε, hloc⟩ := local_taylor2 hK hc
  have hR : PB (fun s => F s - F K - deriv F K * (s - K) - c2 * (s - K) ^ 2) :=
    ((hF.sub (PB.const _)).sub ((PB.id'.sub (PB.const K)).const_mul _)).sub
      (((PB.id'.sub (PB.const K)).pow 2).const_mul c2)
  obtain ⟨M', q, h⟩ := tail_of_local hε hR hloc
  exact ⟨c2, M', q, h⟩

/-- drop one order of a polynomial-tail expansion. -/
theorem lower_order {F : ℝ → ℝ} {K c M : ℝ} {a q : ℕ}
    (h : ∀ s, |F s - c * (s - K) ^ a| ≤ M * (|s - K| ^ (a + 1) * (1 + (s - K) ^ 2) ^ q)) :
    ∃ M' : ℝ, ∀ s, |F s| ≤ M' * (|s - K| ^ a * (1 + (s - K) ^ 2) ^ (q + 1)) := by
  refine ⟨|c| + |M|, fun s => ?_⟩
  set d := |s - K|
  have hd0 : 0 ≤ d := abs_nonneg _
  have hsq : (s - K) ^ 2 = d ^ 2 := (sq_abs _).symm
  rw [hsq]
  have hs := h s
  rw [hsq] at hs
  have hA : 1 ≤ 1 + d ^ 2 := by nlinarith
  have hQ : (1 : ℝ) ≤ (1 + d ^ 2) ^ q := one_le_pow₀ hA
  have hd1 : d ≤ 1 + d ^ 2 := by nlinarith
  have hca : |c * (s - K) ^ a| = |c| * d ^ a := by rw [abs_mul, abs_pow]
  have e1 : |c| * d ^ a ≤ |c| * (d ^ a * (1 + d ^ 2) ^ (q + 1)) := by
    gcongr; exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hA)
  have e2 : M * (d ^ (a + 1) * (1 + d ^ 2) ^ q) ≤ |M| * (d ^ a * (1 + d ^ 2) ^ (q + 1)) := by
    calc M * (d ^ (a + 1) * (1 + d ^ 2) ^ q) ≤ |M| * (d ^ (a + 1) * (1 + d ^ 2) ^ q) := by
          gcongr; exact le_abs_self M
      _ = |M| * (d ^ a * (d * (1 + d ^ 2) ^ q)) := by ring
      _ ≤ |M| * (d ^ a * ((1 + d ^ 2) * (1 + d ^ 2) ^ q)) := by gcongr
      _ = _ := by ring
  calc |F s| ≤ |F s - c * (s - K) ^ a| + |c * (s - K) ^ a| := by
        have := abs_add_le (F s - c * (s - K) ^ a) (c * (s - K) ^ a); simpa using this
    _ ≤ M * (d ^ (a + 1) * (1 + d ^ 2) ^ q) + |c| * d ^ a := by rw [hca]; linarith
    _ ≤ _ := by linarith

end growth


section rowLaw

open Complex Matrix
open scoped RealInnerProductSpace

/-- characteristic integral of a linear form of iid standard Gaussians (from c38c8303). -/
lemma integral_cexp_linear {κ : Type*} [Fintype κ] (c : κ → ℝ) :
    ∫ u : κ → ℝ, cexp ((∑ k, c k * u k : ℝ) * I) ∂(Measure.pi fun _ : κ => gaussianReal 0 1)
      = cexp (-(∑ k, c k ^ 2 : ℝ) / 2) := by
  have h := integral_fintype_prod_eq_prod (𝕜 := ℂ)
    (fun k (x : ℝ) => cexp ((c k * x : ℝ) * I)) (μ := fun _ : κ => gaussianReal 0 1)
  have h2 : ∀ k, ∫ x, cexp ((c k * x : ℝ) * I) ∂gaussianReal 0 1 = cexp (-(c k ^ 2 : ℝ) / 2) := by
    intro k
    have := charFun_gaussianReal (μ := 0) (v := 1) (c k)
    rw [charFun_apply_real] at this
    push_cast at this ⊢
    rw [this]; congr 1; ring
  calc ∫ u : κ → ℝ, cexp ((∑ k, c k * u k : ℝ) * I) ∂(Measure.pi fun _ : κ => gaussianReal 0 1)
      = ∫ u : κ → ℝ, ∏ k, cexp ((c k * u k : ℝ) * I)
          ∂(Measure.pi fun _ : κ => gaussianReal 0 1) := by
        congr 1 with u
        rw [← Complex.exp_sum]
        congr 1
        push_cast
        rw [Finset.sum_mul]
    _ = ∏ k, cexp (-(c k ^ 2 : ℝ) / 2) := by rw [h]; simp only [h2]
    _ = cexp (-(∑ k, c k ^ 2 : ℝ) / 2) := by
        rw [← Complex.exp_sum]
        congr 1
        push_cast
        simp only [neg_div, Finset.sum_neg_distrib, Finset.sum_div]

lemma map_pi_gaussian_linear {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix ι κ ℝ) :
    (Measure.pi fun _ : κ => gaussianReal 0 1).map (fun u => WithLp.toLp 2 (A *ᵥ u)) =
      multivariateGaussian 0 (A * A.transpose) := by
  have hPSD : (A * A.transpose).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose A
  have hmeas : Measurable (fun u : κ → ℝ => WithLp.toLp 2 (A *ᵥ u)) :=
    ((PiLp.continuous_toLp 2 _).comp (Continuous.matrix_mulVec continuous_const continuous_id)).measurable
  apply Measure.ext_of_charFun
  funext s
  rw [charFun_multivariateGaussian hPSD, charFun_apply,
    integral_map hmeas.aemeasurable (by fun_prop)]
  have hinner : ∀ u : κ → ℝ,
      ⟪WithLp.toLp 2 (A *ᵥ u), s⟫ = ∑ k, (A.transpose *ᵥ s.ofLp) k * u k := by
    intro u
    simp only [PiLp.inner_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      RCLike.inner_apply, conj_trivial, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  simp_rw [hinner]
  rw [integral_cexp_linear]
  have hq : ∑ k, (A.transpose *ᵥ s.ofLp) k ^ 2 = s.ofLp ⬝ᵥ (A * A.transpose) *ᵥ s.ofLp := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    simp [dotProduct, sq]
  rw [hq]
  congr 1
  simp [neg_div]

lemma map_pi_gaussian_linear_eval {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix ι κ ℝ) (i : ι) :
    (Measure.pi fun _ : κ => gaussianReal 0 1).map (fun u => (A *ᵥ u) i) =
      gaussianReal 0 ((A * A.transpose) i i).toNNReal := by
  have hPSD : (A * A.transpose).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose A
  have hmeas : Measurable (fun u : κ → ℝ => WithLp.toLp 2 (A *ᵥ u)) :=
    ((PiLp.continuous_toLp 2 _).comp (Continuous.matrix_mulVec continuous_const continuous_id)).measurable
  rw [show (fun u => (A *ᵥ u) i) =
      (fun v : EuclideanSpace ℝ ι => v i) ∘ (fun u => WithLp.toLp 2 (A *ᵥ u)) from rfl,
    ← Measure.map_map (PiLp.continuous_apply 2 _ i).measurable hmeas, map_pi_gaussian_linear,
    (measurePreserving_eval_multivariateGaussian hPSD).map_eq]
  simp

/-- law of a linear form of iid standard Gaussians. -/
lemma rowLaw {κ : Type*} [Fintype κ] (c : κ → ℝ) :
    (Measure.pi fun _ : κ => gaussianReal 0 1).map (fun u => ∑ q, c q * u q) =
      gaussianReal 0 (∑ q, c q ^ 2).toNNReal := by
  have h := map_pi_gaussian_linear_eval (ι := Fin 1) (Matrix.of fun (_ : Fin 1) q => c q) 0
  have e1 : (fun u : κ → ℝ => ((Matrix.of fun (_ : Fin 1) q => c q) *ᵥ u) 0) =
      fun u => ∑ q, c q * u q := by
    funext u; simp [Matrix.mulVec, dotProduct]
  have e2 : ((Matrix.of fun (_ : Fin 1) q => c q) *
      (Matrix.of fun (_ : Fin 1) q => c q).transpose) 0 0 = ∑ q, c q ^ 2 := by
    simp [Matrix.mul_apply, sq]
  rw [e1, e2] at h
  exact h

/-- joint law of independent rows. -/
lemma rowsLaw {ι κ : Type*} [Fintype ι] [Fintype κ] (c : κ → ℝ) :
    (Measure.pi fun _ : ι => Measure.pi fun _ : κ => gaussianReal 0 1).map
      (fun Y i => ∑ q, c q * Y i q) =
      Measure.pi fun _ : ι => gaussianReal 0 (∑ q, c q ^ 2).toNNReal := by
  rw [Measure.pi_map_pi (f := fun _ (u : κ → ℝ) => ∑ q, c q * u q)
    (fun _ => (Finset.measurable_sum _ fun q _ => by fun_prop).aemeasurable)]
  simp only [rowLaw]

end rowLaw

section condGauss

variable {n : ℕ → ℕ} {L : ℕ}

lemma measurable_mlpZ (Cb CW : ℝ) {σ : ℝ → ℝ} (hσ : Measurable σ) (x : Fin (n 0) → ℝ) :
    ∀ (ℓ : ℕ) (i : Fin (n ℓ)), Measurable (fun θ : Params n L => mlpZ Cb CW σ θ x ℓ i)
  | 0, _ => measurable_const
  | ℓ + 1, i => by
    have ih := measurable_mlpZ Cb CW hσ x ℓ
    have hb : Measurable (fun θ : Params n L => mlpBias Cb θ ℓ i) := by
      by_cases h : ℓ < L + 1
      · simp only [mlpBias, dif_pos h]; exact (measurable_pi_apply _).const_mul _
      · simp only [mlpBias, dif_neg h]; exact measurable_const
    have hw : ∀ j, Measurable (fun θ : Params n L => mlpWeight CW θ ℓ i j) := by
      intro j
      by_cases h : ℓ < L + 1
      · simp only [mlpWeight, dif_pos h]; exact (measurable_pi_apply _).const_mul _
      · simp only [mlpWeight, dif_neg h]; exact measurable_const
    have ha : ∀ j, Measurable (fun θ : Params n L => act Cb CW σ θ x ℓ j) := by
      intro j
      by_cases h : ℓ = 0
      · simp only [act, if_pos h]; exact ih j
      · simp only [act, if_neg h]; exact hσ.comp (ih j)
    exact hb.add (Finset.measurable_sum _ fun j _ => (hw j).mul (ha j))

lemma measurable_act (Cb CW : ℝ) {σ : ℝ → ℝ} (hσ : Measurable σ) (x : Fin (n 0) → ℝ) (m : ℕ)
    (j : Fin (n m)) : Measurable (fun θ : Params n L => act Cb CW σ θ x m j) := by
  by_cases h : m = 0
  · simp only [act, if_pos h]; exact measurable_mlpZ Cb CW hσ x m j
  · simp only [act, if_neg h]; exact hσ.comp (measurable_mlpZ Cb CW hσ x m j)

/-- parameters with the layer-`m` block zeroed and the rest given by `r`. -/
noncomputable def fill (m : ℕ) (r : {a : ParamIndex n L // ¬ layerOf a = m} → ℝ) : Params n L :=
  fun a => if h : layerOf a = m then 0 else r ⟨a, h⟩

lemma act_eq_fill (Cb CW : ℝ) (σ : ℝ → ℝ) (x : Fin (n 0) → ℝ) (m : ℕ) (hm : m < L + 1)
    (θ : Params n L) :
    act Cb CW σ θ x m = act Cb CW σ (fill m (splitME m hm θ).2) x m := by
  have h := mlpZ_congr Cb CW σ (θ := θ) (θ' := fill m (splitME m hm θ).2) x m (fun a ha => by
    rw [splitME_apply]; simp only [fill, dif_neg (show ¬ layerOf a = m by omega)])
  funext j; simp only [act, h]

/-- coefficients of a layer-`(m+1)` preactivation in its (bias, weights) block. -/
noncomputable def coef (Cb CW : ℝ) (n : ℕ → ℕ) (m : ℕ) (a : Fin (n m) → ℝ) :
    Option (Fin (n m)) → ℝ
  | none => Real.sqrt Cb
  | some j => Real.sqrt (CW / n m) * a j

lemma mlpZ_succ_split (Cb CW : ℝ) (σ : ℝ → ℝ) (x : Fin (n 0) → ℝ) (m : ℕ) (hm : m < L + 1)
    (θ : Params n L) (i : Fin (n (m + 1))) :
    mlpZ Cb CW σ θ x (m + 1) i =
      ∑ q, coef Cb CW n m (act Cb CW σ θ x m) q * (splitME m hm θ).1 i q := by
  rw [mlpZ_succ, Fintype.sum_option, splitME_apply]
  simp only [mlpBias, mlpWeight, dif_pos hm, coef, blk]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

lemma sum_coef_sq (Cb CW : ℝ) (hCb : 0 ≤ Cb) (hCW : 0 ≤ CW) (n : ℕ → ℕ) (m : ℕ)
    (a : Fin (n m) → ℝ) :
    ∑ q, coef Cb CW n m a q ^ 2 = Cb + CW / n m * ∑ j, a j ^ 2 := by
  rw [Fintype.sum_option]
  simp only [coef, mul_pow, Real.sq_sqrt hCb, Real.sq_sqrt (div_nonneg hCW (Nat.cast_nonneg _)),
    Finset.mul_sum]

/-- F1: conditional Gaussianity of layer `m+1` given the earlier layers. -/
theorem condGauss_integral (Cb CW : ℝ) (hCb : 0 ≤ Cb) (hCW : 0 ≤ CW) (σ : ℝ → ℝ)
    (x : Fin (n 0) → ℝ) (m : ℕ) (hm : m < L + 1) {Φ : (Fin (n (m + 1)) → ℝ) → ℝ}
    (hΦ : Measurable Φ)
    (hint : Integrable (fun θ => Φ (mlpZ Cb CW σ θ x (m + 1))) (stdGaussianParams n L)) :
    Integrable (fun θ => ∫ y, Φ y ∂(Measure.pi fun _ : Fin (n (m + 1)) =>
        gaussianReal 0 (Cb + CW / n m * ∑ j, act Cb CW σ θ x m j ^ 2).toNNReal))
      (stdGaussianParams n L) ∧
    ∫ θ, Φ (mlpZ Cb CW σ θ x (m + 1)) ∂(stdGaussianParams n L) =
      ∫ θ, (∫ y, Φ y ∂(Measure.pi fun _ : Fin (n (m + 1)) =>
        gaussianReal 0 (Cb + CW / n m * ∑ j, act Cb CW σ θ x m j ^ 2).toNNReal))
        ∂(stdGaussianParams n L) := by
  have hmp := measurePreserving_splitME (n := n) (L := L) m hm
  let A : ({a : ParamIndex n L // ¬ layerOf a = m} → ℝ) → Fin (n m) → ℝ :=
    fun r => act Cb CW σ (fill m r) x m
  let G : (Fin (n m) → ℝ) → ℝ := fun a => ∫ y, Φ y ∂(Measure.pi fun _ : Fin (n (m + 1)) =>
        gaussianReal 0 (Cb + CW / n m * ∑ j, a j ^ 2).toNNReal)
  let F : (Fin (n (m + 1)) → Option (Fin (n m)) → ℝ) ×
      ({a : ParamIndex n L // ¬ layerOf a = m} → ℝ) → ℝ :=
    fun p => Φ (fun i => ∑ q, coef Cb CW n m (A p.2) q * p.1 i q)
  have hFe : ∀ θ, F (splitME m hm θ) = Φ (mlpZ Cb CW σ θ x (m + 1)) := by
    intro θ
    simp only [F, A]
    congr 1; funext i
    rw [mlpZ_succ_split Cb CW σ x m hm θ i, ← act_eq_fill]
  have hGe : ∀ θ, G (A (splitME m hm θ).2) = G (act Cb CW σ θ x m) := by
    intro θ; simp only [A]; rw [← act_eq_fill]
  have hFint : Integrable F
      ((Measure.pi fun _ : Fin (n (m + 1)) => Measure.pi fun _ : Option (Fin (n m)) =>
          gaussianReal 0 1).prod
        (Measure.pi fun _ : {a : ParamIndex n L // ¬ layerOf a = m} => gaussianReal 0 1)) := by
    rw [← hmp.integrable_comp_emb (splitME m hm).measurableEmbedding]
    refine hint.congr (Filter.Eventually.of_forall fun θ => ?_)
    simp only [Function.comp]; rw [hFe]
  have hinner : ∀ r, ∫ Y, F (Y, r) ∂(Measure.pi fun _ : Fin (n (m + 1)) =>
      Measure.pi fun _ : Option (Fin (n m)) => gaussianReal 0 1) = G (A r) := by
    intro r
    have hmY : Measurable (fun Y : Fin (n (m + 1)) → Option (Fin (n m)) → ℝ =>
        fun i => ∑ q, coef Cb CW n m (A r) q * Y i q) := by
      refine measurable_pi_lambda _ fun i => Finset.measurable_sum _ fun q _ => ?_
      fun_prop
    simp only [F, G]
    rw [← sum_coef_sq Cb CW hCb hCW n m (A r), ← rowsLaw,
      integral_map hmY.aemeasurable hΦ.aestronglyMeasurable]
  have hGint : Integrable (fun r => G (A r))
      (Measure.pi fun _ : {a : ParamIndex n L // ¬ layerOf a = m} => gaussianReal 0 1) := by
    have := hFint.integral_prod_right
    simpa only [hinner] using this
  constructor
  · have h2 := hGint.comp_snd (Measure.pi fun _ : Fin (n (m + 1)) =>
      Measure.pi fun _ : Option (Fin (n m)) => gaussianReal 0 1)
    rw [← hmp.integrable_comp_emb (splitME m hm).measurableEmbedding] at h2
    refine h2.congr (Filter.Eventually.of_forall fun θ => ?_)
    simp only [Function.comp]; exact hGe θ
  · calc ∫ θ, Φ (mlpZ Cb CW σ θ x (m + 1)) ∂(stdGaussianParams n L)
        = ∫ θ, F (splitME m hm θ) ∂(stdGaussianParams n L) := by simp only [hFe]
      _ = ∫ p, F p ∂((Measure.pi fun _ : Fin (n (m + 1)) => Measure.pi fun _ : Option (Fin (n m)) =>
          gaussianReal 0 1).prod
          (Measure.pi fun _ : {a : ParamIndex n L // ¬ layerOf a = m} => gaussianReal 0 1)) :=
          hmp.integral_comp' F
      _ = ∫ r, ∫ Y, F (Y, r) ∂(Measure.pi fun _ : Fin (n (m + 1)) =>
            Measure.pi fun _ : Option (Fin (n m)) => gaussianReal 0 1)
            ∂(Measure.pi fun _ : {a : ParamIndex n L // ¬ layerOf a = m} => gaussianReal 0 1) :=
          integral_prod_symm F hFint
      _ = ∫ r, G (A r)
            ∂(Measure.pi fun _ : {a : ParamIndex n L // ¬ layerOf a = m} => gaussianReal 0 1) := by
          simp only [hinner]
      _ = ∫ p, (1 : ℝ) * G (A p.2)
            ∂((Measure.pi fun _ : Fin (n (m + 1)) => Measure.pi fun _ : Option (Fin (n m)) =>
              gaussianReal 0 1).prod
            (Measure.pi fun _ : {a : ParamIndex n L // ¬ layerOf a = m} => gaussianReal 0 1)) := by
          rw [integral_prod_mul (fun _ => (1 : ℝ)) (fun r => G (A r))]; simp
      _ = ∫ θ, (1 : ℝ) * G (A (splitME m hm θ).2) ∂(stdGaussianParams n L) :=
          (hmp.integral_comp' (fun p => (1 : ℝ) * G (A p.2))).symm
      _ = _ := by simp only [one_mul, hGe]; rfl

end condGauss

section integrability

/-- polynomially bounded measurable functions of finitely many real parameters. -/
def PT {ι : Type*} [Fintype ι] (F : (ι → ℝ) → ℝ) : Prop :=
  Measurable F ∧ ∃ C : ℝ, ∃ p : ℕ, ∀ θ, |F θ| ≤ C * (1 + ∑ a, |θ a|) ^ p

variable {ι : Type*} [Fintype ι]

lemma one_le_base (θ : ι → ℝ) : (1 : ℝ) ≤ 1 + ∑ a, |θ a| := by
  have : 0 ≤ ∑ a, |θ a| := Finset.sum_nonneg fun a _ => abs_nonneg _
  linarith

lemma PT.nonneg_const {F : (ι → ℝ) → ℝ} {C : ℝ} {p : ℕ}
    (h : ∀ θ, |F θ| ≤ C * (1 + ∑ a, |θ a|) ^ p) : 0 ≤ C := by
  have h0 := h 0
  simp only [Pi.zero_apply, abs_zero, Finset.sum_const_zero, add_zero, one_pow, mul_one] at h0
  exact (abs_nonneg _).trans h0

lemma PT.const (c : ℝ) : PT (ι := ι) (fun _ => c) := ⟨measurable_const, |c|, 0, fun θ => by simp⟩

lemma PT.coord (a : ι) : PT (fun θ : ι → ℝ => θ a) := by
  refine ⟨measurable_pi_apply a, 1, 1, fun θ => ?_⟩
  have : |θ a| ≤ ∑ b, |θ b| :=
    Finset.single_le_sum (f := fun b => |θ b|) (fun b _ => abs_nonneg _) (Finset.mem_univ a)
  simp only [pow_one, one_mul]; linarith

lemma PT.mul {F G : (ι → ℝ) → ℝ} (hF : PT F) (hG : PT G) : PT (fun θ => F θ * G θ) := by
  obtain ⟨hFm, C1, k1, h1⟩ := hF
  obtain ⟨hGm, C2, k2, h2⟩ := hG
  refine ⟨hFm.mul hGm, C1 * C2, k1 + k2, fun θ => ?_⟩
  rw [abs_mul, pow_add]
  have := PT.nonneg_const h1
  have hB := one_le_base θ
  calc |F θ| * |G θ| ≤ (C1 * (1 + ∑ a, |θ a|) ^ k1) * (C2 * (1 + ∑ a, |θ a|) ^ k2) :=
        mul_le_mul (h1 θ) (h2 θ) (abs_nonneg _) (by positivity)
    _ = _ := by ring

lemma PT.add {F G : (ι → ℝ) → ℝ} (hF : PT F) (hG : PT G) : PT (fun θ => F θ + G θ) := by
  obtain ⟨hFm, C1, k1, h1⟩ := hF
  obtain ⟨hGm, C2, k2, h2⟩ := hG
  refine ⟨hFm.add hGm, C1 + C2, k1 + k2, fun θ => ?_⟩
  have c1 := PT.nonneg_const h1
  have c2 := PT.nonneg_const h2
  have hB := one_le_base θ
  have e1 : (1 + ∑ a, |θ a|) ^ k1 ≤ (1 + ∑ a, |θ a|) ^ (k1 + k2) := pow_le_pow_right₀ hB (by omega)
  have e2 : (1 + ∑ a, |θ a|) ^ k2 ≤ (1 + ∑ a, |θ a|) ^ (k1 + k2) := pow_le_pow_right₀ hB (by omega)
  calc |F θ + G θ| ≤ |F θ| + |G θ| := abs_add_le _ _
    _ ≤ C1 * (1 + ∑ a, |θ a|) ^ k1 + C2 * (1 + ∑ a, |θ a|) ^ k2 := add_le_add (h1 θ) (h2 θ)
    _ ≤ C1 * (1 + ∑ a, |θ a|) ^ (k1 + k2) + C2 * (1 + ∑ a, |θ a|) ^ (k1 + k2) := by gcongr
    _ = _ := by ring

lemma PT.sum {κ : Type*} (s : Finset κ) {F : κ → (ι → ℝ) → ℝ} (h : ∀ k ∈ s, PT (F k)) :
    PT (fun θ => ∑ k ∈ s, F k θ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PT.const (ι := ι) 0
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

lemma PT.comp {f : ℝ → ℝ} (hf : PB f) {F : (ι → ℝ) → ℝ} (hF : PT F) : PT (fun θ => f (F θ)) := by
  obtain ⟨hfm, Cf, k, hfb⟩ := hf
  obtain ⟨hFm, C, p, hFb⟩ := hF
  have hCf := PB.nonneg_const hfb
  have hC := PT.nonneg_const hFb
  refine ⟨hfm.comp hFm, Cf * (1 + C) ^ k, p * k, fun θ => ?_⟩
  have hB := one_le_base θ
  have hX : (1:ℝ) ≤ (1 + ∑ a, |θ a|) ^ p := one_le_pow₀ hB
  have e : 1 + |F θ| ≤ (1 + C) * (1 + ∑ a, |θ a|) ^ p := by nlinarith [hFb θ]
  calc |f (F θ)| ≤ Cf * (1 + |F θ|) ^ k := hfb _
    _ ≤ Cf * ((1 + C) * (1 + ∑ a, |θ a|) ^ p) ^ k := by gcongr
    _ = Cf * (1 + C) ^ k * (1 + ∑ a, |θ a|) ^ (p * k) := by rw [mul_pow, ← pow_mul]; ring

lemma PT.integrable {F : (ι → ℝ) → ℝ} (hF : PT F) :
    Integrable F (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  obtain ⟨hFm, C, p, hFb⟩ := hF
  have hC := PT.nonneg_const hFb
  have hcoord : ∀ a, Integrable (fun θ : ι → ℝ => |θ a| ^ (p + 1))
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
    intro a
    have h1 : Integrable (fun t : ℝ => |t| ^ (p + 1)) (gaussianReal 0 1) := by
      have hm : MemLp (id : ℝ → ℝ) ((p + 1 : ℕ) : ENNReal) (gaussianReal 0 1) := by
        simpa using memLp_id_gaussianReal (μ := 0) (v := 1) ((p + 1 : ℕ) : NNReal)
      simpa [Real.norm_eq_abs] using hm.integrable_norm_pow'
    exact (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) a).integrable_comp_of_integrable h1
  have hpm : ∀ θ : ι → ℝ, (1 + ∑ a, |θ a|) ^ (p + 1) ≤
      ((Fintype.card ι + 1 : ℕ) : ℝ) ^ p * (1 + ∑ a, |θ a| ^ (p + 1)) := by
    intro θ
    have h := pow_sum_div_card_le_sum_pow (s := (Finset.univ : Finset (Option ι)))
      (f := fun o => Option.elim o 1 (fun a => |θ a|)) (fun o _ => by cases o <;> simp) p
    simp only [Fintype.sum_option, Option.elim, one_pow, Finset.card_univ, Fintype.card_option] at h
    rw [div_le_iff₀ (by positivity)] at h
    push_cast at h ⊢
    linarith
  have hG : Integrable (fun θ : ι → ℝ => C * ((Fintype.card ι + 1 : ℕ) : ℝ) ^ p *
      (1 + ∑ a, |θ a| ^ (p + 1))) (Measure.pi fun _ : ι => gaussianReal 0 1) :=
    ((integrable_const 1).add (integrable_finsetSum _ fun a _ => hcoord a)).const_mul _
  refine hG.mono' hFm.aestronglyMeasurable (Filter.Eventually.of_forall fun θ => ?_)
  rw [Real.norm_eq_abs]
  have hB := one_le_base θ
  calc |F θ| ≤ C * (1 + ∑ a, |θ a|) ^ p := hFb θ
    _ ≤ C * (1 + ∑ a, |θ a|) ^ (p + 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB (Nat.le_succ p)) hC
    _ ≤ C * (((Fintype.card ι + 1 : ℕ) : ℝ) ^ p * (1 + ∑ a, |θ a| ^ (p + 1))) :=
        mul_le_mul_of_nonneg_left (hpm θ) hC
    _ = _ := by ring

end integrability

section network

variable {n : ℕ → ℕ} {L : ℕ}

lemma PT_mlpZ (Cb CW : ℝ) {σ : ℝ → ℝ} (hσ : PB σ) (x : Fin (n 0) → ℝ) :
    ∀ (ℓ : ℕ) (i : Fin (n ℓ)), PT (fun θ : Params n L => mlpZ Cb CW σ θ x ℓ i)
  | 0, i => PT.const (x i)
  | ℓ + 1, i => by
    have ih := PT_mlpZ Cb CW hσ x ℓ
    have hb : PT (fun θ : Params n L => mlpBias Cb θ ℓ i) := by
      by_cases h : ℓ < L + 1
      · simp only [mlpBias, dif_pos h]; exact (PT.const _).mul (PT.coord _)
      · simp only [mlpBias, dif_neg h]; exact PT.const 0
    have hw : ∀ j, PT (fun θ : Params n L => mlpWeight CW θ ℓ i j) := by
      intro j
      by_cases h : ℓ < L + 1
      · simp only [mlpWeight, dif_pos h]; exact (PT.const _).mul (PT.coord _)
      · simp only [mlpWeight, dif_neg h]; exact PT.const 0
    have ha : ∀ j, PT (fun θ : Params n L => act Cb CW σ θ x ℓ j) := by
      intro j
      by_cases h : ℓ = 0
      · simp only [act, if_pos h]; exact ih j
      · simp only [act, if_neg h]; exact PT.comp hσ (ih j)
    exact hb.add (PT.sum _ fun j _ => (hw j).mul (ha j))

lemma PT_act (Cb CW : ℝ) {σ : ℝ → ℝ} (hσ : PB σ) (x : Fin (n 0) → ℝ) (m : ℕ) (j : Fin (n m)) :
    PT (fun θ : Params n L => act Cb CW σ θ x m j) := by
  by_cases h : m = 0
  · simp only [act, if_pos h]; exact PT_mlpZ Cb CW hσ x m j
  · simp only [act, if_neg h]; exact PT.comp hσ (PT_mlpZ Cb CW hσ x m j)

/-- the conditional variance of layer `m+1`: `S_m = C_b + C_W/n_m Σ_j act_j²`. -/
noncomputable def Sv (Cb CW : ℝ) (σ : ℝ → ℝ) (θ : Params n L) (x : Fin (n 0) → ℝ) (m : ℕ) : ℝ :=
  Cb + CW / n m * ∑ j, act Cb CW σ θ x m j ^ 2

lemma Sv_nonneg {Cb CW : ℝ} (hCb : 0 ≤ Cb) (hCW : 0 ≤ CW) (σ : ℝ → ℝ) (θ : Params n L)
    (x : Fin (n 0) → ℝ) (m : ℕ) : 0 ≤ Sv Cb CW σ θ x m := by
  unfold Sv; positivity

lemma PT_Sv (Cb CW : ℝ) {σ : ℝ → ℝ} (hσ : PB σ) (x : Fin (n 0) → ℝ) (m : ℕ) :
    PT (fun θ : Params n L => Sv Cb CW σ θ x m) :=
  (PT.const Cb).add ((PT.const _).mul (PT.sum _ fun j _ =>
    PT.comp (PB.id'.pow 2) (PT_act Cb CW hσ x m j)))

/-- M7: the normalized fourth cumulant of layer `m+1` is the variance of `S_m`. -/
theorem kappa4_succ {Cb CW : ℝ} (hCb : 0 ≤ Cb) (hCW : 0 ≤ CW) {σ : ℝ → ℝ} (hσ : PB σ)
    (x : Fin (n 0) → ℝ) (m : ℕ) (hm : m < L + 1) (i : Fin (n (m + 1))) :
    kappa4 Cb CW σ n L x (m + 1) i =
      ∫ θ, Sv Cb CW σ θ x m ^ 2 ∂(stdGaussianParams n L) -
        (∫ θ, Sv Cb CW σ θ x m ∂(stdGaussianParams n L)) ^ 2 := by
  have hz := PT_mlpZ (L := L) Cb CW hσ x (m + 1) i
  have h4 := condGauss_integral Cb CW hCb hCW σ x m hm (Φ := fun y => y i ^ 4) (by fun_prop)
    (PT.integrable (PT.comp (PB.id'.pow 4) hz))
  have h2 := condGauss_integral Cb CW hCb hCW σ x m hm (Φ := fun y => y i ^ 2) (by fun_prop)
    (PT.integrable (PT.comp (PB.id'.pow 2) hz))
  have e4 : ∀ θ : Params n L, ∫ y, y i ^ 4 ∂(Measure.pi fun _ : Fin (n (m + 1)) =>
      gaussianReal 0 (Cb + CW / n m * ∑ j, act Cb CW σ θ x m j ^ 2).toNNReal) =
      3 * Sv Cb CW σ θ x m ^ 2 := by
    intro θ
    rw [integral_comp_eval (μ := fun _ => gaussianReal 0 _) (i := i) (f := fun t => t ^ 4)
      (by fun_prop), gauss_mom4, Real.coe_toNNReal _ (show (0:ℝ) ≤ Cb + CW / n m * ∑ j,
        act Cb CW σ θ x m j ^ 2 from Sv_nonneg hCb hCW σ θ x m)]
    rfl
  have e2 : ∀ θ : Params n L, ∫ y, y i ^ 2 ∂(Measure.pi fun _ : Fin (n (m + 1)) =>
      gaussianReal 0 (Cb + CW / n m * ∑ j, act Cb CW σ θ x m j ^ 2).toNNReal) =
      Sv Cb CW σ θ x m := by
    intro θ
    rw [integral_comp_eval (μ := fun _ => gaussianReal 0 _) (i := i) (f := fun t => t ^ 2)
      (by fun_prop), gauss_mom2, Real.coe_toNNReal _ (show (0:ℝ) ≤ Cb + CW / n m * ∑ j,
        act Cb CW σ θ x m j ^ 2 from Sv_nonneg hCb hCW σ θ x m)]
    rfl
  beta_reduce at h4 h2
  unfold kappa4
  rw [h4.2, h2.2]
  simp only [e4, e2]
  rw [integral_const_mul]
  ring

end network

section sums

variable {ν : Measure ℝ} [IsProbabilityMeasure ν]

/-- the empirical sum `Σ_j f(y_j)`. -/
def Tsum (f : ℝ → ℝ) (n : ℕ) (y : Fin n → ℝ) : ℝ := ∑ j, f (y j)

lemma Tsum_succ (f : ℝ → ℝ) (n : ℕ) (y : Fin (n + 1) → ℝ) :
    Tsum f (n + 1) y = f (y 0) + Tsum f n (fun j => y j.succ) := by
  simp only [Tsum, Fin.sum_univ_succ]

lemma piSucc_eq (n : ℕ) (y : Fin (n + 1) → ℝ) :
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0 y = (y 0, fun j => y j.succ) := by
  rw [MeasurableEquiv.piFinSuccAbove_apply]
  ext
  · rfl
  · simp [Fin.insertNthEquiv]; rfl

lemma integral_pi_succ (n : ℕ) (G : ℝ × (Fin n → ℝ) → ℝ) :
    ∫ y, G (y 0, fun j => y j.succ) ∂(Measure.pi fun _ : Fin (n + 1) => ν) =
      ∫ p, G p ∂(ν.prod (Measure.pi fun _ : Fin n => ν)) := by
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0).integral_comp' G
  simp only [piSucc_eq] at h
  exact h

lemma integrable_pi_succ (n : ℕ) {G : ℝ × (Fin n → ℝ) → ℝ}
    (hG : Integrable G (ν.prod (Measure.pi fun _ : Fin n => ν))) :
    Integrable (fun y => G (y 0, fun j => y j.succ)) (Measure.pi fun _ : Fin (n + 1) => ν) := by
  have h := ((measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0).integrable_comp_emb
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).measurableEmbedding).2 hG
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [Function.comp, piSucc_eq]

lemma integral_prod_snd' {n : ℕ} (F : (Fin n → ℝ) → ℝ) :
    ∫ p, F p.2 ∂(ν.prod (Measure.pi fun _ : Fin n => ν)) = ∫ y, F y ∂(Measure.pi fun _ : Fin n => ν) := by
  have := integral_prod_mul (μ := ν) (ν := Measure.pi fun _ : Fin n => ν) (fun _ => (1:ℝ)) F
  simpa using this

lemma integral_prod_fst' {n : ℕ} (F : ℝ → ℝ) :
    ∫ p, F p.1 ∂(ν.prod (Measure.pi fun _ : Fin n => ν)) = ∫ t, F t ∂ν := by
  have := integral_prod_mul (μ := ν) (ν := Measure.pi fun _ : Fin n => ν) F (fun _ => (1:ℝ))
  simpa using this

omit [IsProbabilityMeasure ν] in
lemma integrable_prod_add_pow {f : ℝ → ℝ} (hf : ∀ p : ℕ, Integrable (fun t => f t ^ p) ν) (n : ℕ)
    (hT : ∀ k : ℕ, Integrable (fun y => Tsum f n y ^ k) (Measure.pi fun _ : Fin n => ν)) (k : ℕ) :
    Integrable (fun p : ℝ × (Fin n → ℝ) => (f p.1 + Tsum f n p.2) ^ k)
      (ν.prod (Measure.pi fun _ : Fin n => ν)) := by
  simp only [add_pow]
  exact integrable_finsetSum _ fun l _ => ((hf l).mul_prod (hT (k - l))).mul_const _

lemma integrable_Tsum_pow {f : ℝ → ℝ} (hf : ∀ p : ℕ, Integrable (fun t => f t ^ p) ν) :
    ∀ (n k : ℕ), Integrable (fun y => Tsum f n y ^ k) (Measure.pi fun _ : Fin n => ν)
  | 0, k => by simp [Tsum]
  | n + 1, k => by
    simp only [Tsum_succ]
    exact integrable_pi_succ n (integrable_prod_add_pow hf n (integrable_Tsum_pow hf n) k)

lemma mom_succ {f : ℝ → ℝ} (hf : ∀ p : ℕ, Integrable (fun t => f t ^ p) ν) (n k : ℕ) :
    ∫ y, Tsum f (n + 1) y ^ k ∂(Measure.pi fun _ : Fin (n + 1) => ν) =
      ∑ l ∈ Finset.range (k + 1), (∫ t, f t ^ l ∂ν) *
        (∫ y, Tsum f n y ^ (k - l) ∂(Measure.pi fun _ : Fin n => ν)) * (k.choose l) := by
  have hT := integrable_Tsum_pow hf n
  simp only [Tsum_succ]
  have h := integral_pi_succ (ν := ν) n (fun p => (f p.1 + Tsum f n p.2) ^ k)
  simp only at h
  rw [h]
  simp only [add_pow]
  rw [integral_finsetSum _ (fun l _ => ((hf l).mul_prod (hT (k - l))).mul_const _)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_mul_const]
  congr 1
  exact integral_prod_mul (fun a => f a ^ l) (fun b => Tsum f n b ^ (k - l))

lemma Tsum_mean {f : ℝ → ℝ} (hf : ∀ p : ℕ, Integrable (fun t => f t ^ p) ν)
    (h0 : ∫ t, f t ∂ν = 0) : ∀ n, ∫ y, Tsum f n y ∂(Measure.pi fun _ : Fin n => ν) = 0
  | 0 => by simp [Tsum]
  | n + 1 => by
    have h := mom_succ hf n 1
    have ih := Tsum_mean hf h0 n
    simp only [pow_one] at h ih
    rw [h]
    simp [Finset.sum_range_succ, ih, h0]

lemma Tsum_sq {f : ℝ → ℝ} (hf : ∀ p : ℕ, Integrable (fun t => f t ^ p) ν)
    (h0 : ∫ t, f t ∂ν = 0) : ∀ n : ℕ, ∫ y, Tsum f n y ^ 2 ∂(Measure.pi fun _ : Fin n => ν) =
      n * ∫ t, f t ^ 2 ∂ν
  | 0 => by simp [Tsum]
  | n + 1 => by
    have h := mom_succ hf n 2
    have ih := Tsum_sq hf h0 n
    rw [h]
    simp [Finset.sum_range_succ, ih, h0]
    ring

lemma Tsum_cube {f : ℝ → ℝ} (hf : ∀ p : ℕ, Integrable (fun t => f t ^ p) ν)
    (h0 : ∫ t, f t ∂ν = 0) : ∀ n : ℕ, ∫ y, Tsum f n y ^ 3 ∂(Measure.pi fun _ : Fin n => ν) =
      n * ∫ t, f t ^ 3 ∂ν
  | 0 => by simp [Tsum]
  | n + 1 => by
    have h := mom_succ hf n 3
    have ih := Tsum_cube hf h0 n
    have hm := Tsum_mean hf h0 n
    rw [h]
    simp [Finset.sum_range_succ, ih, h0, hm]
    ring

lemma abs_pow_mul_le (a b : ℝ) (i j : ℕ) : |a| ^ i * |b| ^ j ≤ |a| ^ (i + j) + |b| ^ (i + j) := by
  rcases le_total |a| |b| with h | h
  · calc |a| ^ i * |b| ^ j ≤ |b| ^ i * |b| ^ j := by gcongr
      _ = |b| ^ (i + j) := by rw [pow_add]
      _ ≤ _ := by have := pow_nonneg (abs_nonneg a) (i + j); linarith
  · calc |a| ^ i * |b| ^ j ≤ |a| ^ i * |a| ^ j := by gcongr
      _ = |a| ^ (i + j) := by rw [pow_add]
      _ ≤ _ := by have := pow_nonneg (abs_nonneg b) (i + j); linarith

/-- the pointwise inequality behind the Marcinkiewicz–Zygmund bound. -/
lemma pow_add_le_mz (a b : ℝ) (r : ℕ) :
    (a + b) ^ (2 * r + 2) ≤ b ^ (2 * r + 2) + (2 * r + 2) * (a * b ^ (2 * r + 1)) +
      4 ^ (r + 1) * (a ^ 2 * b ^ (2 * r) + a ^ (2 * r + 2)) := by
  have hX : 0 ≤ a ^ 2 * b ^ (2 * r) + a ^ (2 * r + 2) := by
    have h1 := (even_two_mul r).pow_nonneg b
    have h2 : 0 ≤ a ^ (2 * r + 2) := by
      rw [show 2 * r + 2 = 2 * (r + 1) by ring]; exact (even_two_mul (r + 1)).pow_nonneg a
    positivity
  have hterm : ∀ l ∈ Finset.range (2 * r + 1), a ^ (l + 1 + 1) * b ^ (2 * r + 2 - (l + 1 + 1)) *
      ((2 * r + 2).choose (l + 1 + 1) : ℝ) ≤
      ((2 * r + 2).choose (l + 1 + 1) : ℝ) * (a ^ 2 * b ^ (2 * r) + a ^ (2 * r + 2)) := by
    intro l hl
    have hl' : l ≤ 2 * r := by simp at hl; omega
    have key : a ^ (l + 1 + 1) * b ^ (2 * r + 2 - (l + 1 + 1)) ≤
        a ^ 2 * b ^ (2 * r) + a ^ (2 * r + 2) := by
      have e : 2 * r + 2 - (l + 1 + 1) = 2 * r - l := by omega
      rw [e]
      have h1 : a ^ (l + 1 + 1) * b ^ (2 * r - l) ≤ |a| ^ (l + 1 + 1) * |b| ^ (2 * r - l) := by
        rw [pow_abs, pow_abs, ← abs_mul]; exact le_abs_self _
      have h2 : |a| ^ l * |b| ^ (2 * r - l) ≤ |a| ^ (2 * r) + |b| ^ (2 * r) := by
        have := abs_pow_mul_le a b l (2 * r - l)
        rwa [show l + (2 * r - l) = 2 * r by omega] at this
      have ea : |a| ^ (2 * r) = a ^ (2 * r) := (even_two_mul r).pow_abs a
      have eb : |b| ^ (2 * r) = b ^ (2 * r) := (even_two_mul r).pow_abs b
      have ea2 : |a| ^ 2 = a ^ 2 := sq_abs a
      calc a ^ (l + 1 + 1) * b ^ (2 * r - l) ≤ |a| ^ (l + 1 + 1) * |b| ^ (2 * r - l) := h1
        _ = |a| ^ 2 * (|a| ^ l * |b| ^ (2 * r - l)) := by ring
        _ ≤ |a| ^ 2 * (|a| ^ (2 * r) + |b| ^ (2 * r)) := by gcongr
        _ = a ^ 2 * b ^ (2 * r) + a ^ (2 * r + 2) := by rw [ea, eb, ea2]; ring
    have hc : (0:ℝ) ≤ ((2 * r + 2).choose (l + 1 + 1) : ℝ) := Nat.cast_nonneg _
    calc a ^ (l + 1 + 1) * b ^ (2 * r + 2 - (l + 1 + 1)) * ((2 * r + 2).choose (l + 1 + 1) : ℝ)
        ≤ (a ^ 2 * b ^ (2 * r) + a ^ (2 * r + 2)) * ((2 * r + 2).choose (l + 1 + 1) : ℝ) :=
          mul_le_mul_of_nonneg_right key hc
      _ = _ := by ring
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.sum_mul] at hsum
  have hch : (∑ l ∈ Finset.range (2 * r + 1), ((2 * r + 2).choose (l + 1 + 1) : ℝ)) ≤ 4 ^ (r + 1) := by
    have h := Nat.sum_range_choose (2 * r + 2)
    rw [Finset.sum_range_succ', Finset.sum_range_succ'] at h
    have hle : (∑ l ∈ Finset.range (2 * r + 1), (2 * r + 2).choose (l + 1 + 1)) ≤ 2 ^ (2 * r + 2) := by
      omega
    have h4 : ((2 ^ (2 * r + 2) : ℕ) : ℝ) = 4 ^ (r + 1) := by
      push_cast; rw [show 2 * r + 2 = 2 * (r + 1) by ring, pow_mul]; norm_num
    rw [← h4]; exact_mod_cast hle
  have hS := hsum.trans (mul_le_mul_of_nonneg_right hch hX)
  rw [add_pow, Finset.sum_range_succ', Finset.sum_range_succ']
  have t1 : a ^ (0 + 1) * b ^ (2 * r + 2 - (0 + 1)) * ((2 * r + 2).choose (0 + 1) : ℝ) =
      (2 * r + 2) * (a * b ^ (2 * r + 1)) := by
    simp only [zero_add, pow_one, Nat.choose_one_right]
    rw [show 2 * r + 2 - 1 = 2 * r + 1 by omega]; push_cast; ring
  have t0 : a ^ 0 * b ^ (2 * r + 2 - 0) * ((2 * r + 2).choose 0 : ℝ) = b ^ (2 * r + 2) := by simp
  rw [t1, t0]
  linarith

/-- Marcinkiewicz–Zygmund constants. -/
def mzB (β : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | r + 1 => 4 ^ (r + 1) * (mzB β r * β 1 + β (r + 1))

lemma mzB_nonneg {β : ℕ → ℝ} (hβ : ∀ j, 0 ≤ β j) : ∀ r, 0 ≤ mzB β r
  | 0 => by simp [mzB]
  | r + 1 => by
    have := mzB_nonneg hβ r
    have := hβ 1
    have := hβ (r + 1)
    simp only [mzB]; positivity

/-- Marcinkiewicz–Zygmund: `E (Σ_j X_j)^{2r} ≤ n^r B_r` for iid centered `X_j`. -/
theorem mz_bound {f : ℝ → ℝ} (hf : ∀ p : ℕ, Integrable (fun t => f t ^ p) ν)
    (h0 : ∫ t, f t ∂ν = 0) {β : ℕ → ℝ} (hβ0 : ∀ j, 0 ≤ β j)
    (hβ : ∀ j, ∫ t, f t ^ (2 * j) ∂ν ≤ β j) :
    ∀ (r n : ℕ), ∫ y, Tsum f n y ^ (2 * r) ∂(Measure.pi fun _ : Fin n => ν) ≤ (n : ℝ) ^ r * mzB β r
  | 0, n => by simp [mzB]
  | r + 1, n => by
    have ihr := mz_bound hf h0 hβ0 hβ r
    have hB := mzB_nonneg hβ0 r
    have hb1 := hβ0 1
    have hbr := hβ0 (r + 1)
    have hX : 0 ≤ mzB β r * β 1 := mul_nonneg hB hb1
    have hm2 : ∫ t, f t ^ 2 ∂ν ≤ β 1 := by simpa using hβ 1
    have hmr : ∫ t, f t ^ (2 * r + 2) ∂ν ≤ β (r + 1) := by
      have := hβ (r + 1); rwa [show 2 * (r + 1) = 2 * r + 2 by ring] at this
    have h4 : (0:ℝ) ≤ 4 ^ (r + 1) := by positivity
    have claim : ∀ n : ℕ, ∫ y, Tsum f n y ^ (2 * r + 2) ∂(Measure.pi fun _ : Fin n => ν) ≤
        n * (4 ^ (r + 1) * ((n : ℝ) ^ r * (mzB β r * β 1) + β (r + 1))) := by
      intro n
      induction n with
      | zero => simp [Tsum]
      | succ n ihn =>
        have hT := integrable_Tsum_pow hf n
        simp only [Tsum_succ]
        have h := integral_pi_succ (ν := ν) n (fun p => (f p.1 + Tsum f n p.2) ^ (2 * r + 2))
        simp only at h
        rw [h]
        have i1 : Integrable (fun p : ℝ × (Fin n → ℝ) => Tsum f n p.2 ^ (2 * r + 2))
            (ν.prod (Measure.pi fun _ : Fin n => ν)) := (hT _).comp_snd ν
        have i2 : Integrable (fun p : ℝ × (Fin n → ℝ) => f p.1 * Tsum f n p.2 ^ (2 * r + 1))
            (ν.prod (Measure.pi fun _ : Fin n => ν)) :=
          (by simpa using hf 1 : Integrable f ν).mul_prod (hT _)
        have i3 : Integrable (fun p : ℝ × (Fin n → ℝ) => f p.1 ^ 2 * Tsum f n p.2 ^ (2 * r))
            (ν.prod (Measure.pi fun _ : Fin n => ν)) := (hf 2).mul_prod (hT _)
        have i4 : Integrable (fun p : ℝ × (Fin n → ℝ) => f p.1 ^ (2 * r + 2))
            (ν.prod (Measure.pi fun _ : Fin n => ν)) := (hf _).comp_fst _
        have iR : Integrable (fun p : ℝ × (Fin n → ℝ) => Tsum f n p.2 ^ (2 * r + 2) +
            (2 * r + 2) * (f p.1 * Tsum f n p.2 ^ (2 * r + 1)) +
            4 ^ (r + 1) * (f p.1 ^ 2 * Tsum f n p.2 ^ (2 * r) + f p.1 ^ (2 * r + 2)))
            (ν.prod (Measure.pi fun _ : Fin n => ν)) :=
          (i1.add (i2.const_mul (2 * r + 2))).add ((i3.add i4).const_mul (4 ^ (r + 1)))
        have hle := integral_mono (integrable_prod_add_pow hf n hT (2 * r + 2)) iR
          (fun p => pow_add_le_mz (f p.1) (Tsum f n p.2) r)
        refine hle.trans ?_
        rw [integral_add ?_ ?_, integral_add ?_ ?_, integral_const_mul, integral_const_mul,
          integral_add ?_ ?_]
        rotate_left
        · exact i3
        · exact i4
        · exact i1
        · exact i2.const_mul _
        · exact i1.add (i2.const_mul _)
        · exact (i3.add i4).const_mul _
        have e1 : ∫ p : ℝ × (Fin n → ℝ), Tsum f n p.2 ^ (2 * r + 2)
            ∂(ν.prod (Measure.pi fun _ : Fin n => ν)) =
            ∫ y, Tsum f n y ^ (2 * r + 2) ∂(Measure.pi fun _ : Fin n => ν) :=
          integral_prod_snd' (fun y => Tsum f n y ^ (2 * r + 2))
        have e2 : ∫ p : ℝ × (Fin n → ℝ), f p.1 * Tsum f n p.2 ^ (2 * r + 1)
            ∂(ν.prod (Measure.pi fun _ : Fin n => ν)) =
            (∫ t, f t ∂ν) * ∫ y, Tsum f n y ^ (2 * r + 1) ∂(Measure.pi fun _ : Fin n => ν) :=
          integral_prod_mul (fun a => f a) (fun b => Tsum f n b ^ (2 * r + 1))
        have e3 : ∫ p : ℝ × (Fin n → ℝ), f p.1 ^ 2 * Tsum f n p.2 ^ (2 * r)
            ∂(ν.prod (Measure.pi fun _ : Fin n => ν)) =
            (∫ t, f t ^ 2 ∂ν) * ∫ y, Tsum f n y ^ (2 * r) ∂(Measure.pi fun _ : Fin n => ν) :=
          integral_prod_mul (fun a => f a ^ 2) (fun b => Tsum f n b ^ (2 * r))
        have e4 : ∫ p : ℝ × (Fin n → ℝ), f p.1 ^ (2 * r + 2)
            ∂(ν.prod (Measure.pi fun _ : Fin n => ν)) = ∫ t, f t ^ (2 * r + 2) ∂ν :=
          integral_prod_fst' (fun t => f t ^ (2 * r + 2))
        rw [e1, e2, e3, e4, h0]
        have hTnn : 0 ≤ ∫ y, Tsum f n y ^ (2 * r) ∂(Measure.pi fun _ : Fin n => ν) :=
          integral_nonneg fun y => (even_two_mul r).pow_nonneg _
        have hprod : (∫ t, f t ^ 2 ∂ν) * ∫ y, Tsum f n y ^ (2 * r) ∂(Measure.pi fun _ : Fin n => ν)
            ≤ (n : ℝ) ^ r * (mzB β r * β 1) := by
          have := mul_le_mul hm2 (ihr n) hTnn hb1
          linarith [show β 1 * ((n : ℝ) ^ r * mzB β r) = (n : ℝ) ^ r * (mzB β r * β 1) by ring]
        have a1 : 4 ^ (r + 1) * ((∫ t, f t ^ 2 ∂ν) *
            ∫ y, Tsum f n y ^ (2 * r) ∂(Measure.pi fun _ : Fin n => ν) + ∫ t, f t ^ (2 * r + 2) ∂ν) ≤
            4 ^ (r + 1) * ((n : ℝ) ^ r * (mzB β r * β 1) + β (r + 1)) :=
          mul_le_mul_of_nonneg_left (add_le_add hprod hmr) h4
        have hn : (n : ℝ) ^ r ≤ ((n : ℝ) + 1) ^ r :=
          pow_le_pow_left₀ (Nat.cast_nonneg n) (by linarith) r
        have a2 : ((n : ℝ) + 1) * (4 ^ (r + 1) * ((n : ℝ) ^ r * (mzB β r * β 1) + β (r + 1))) ≤
            ((n : ℝ) + 1) * (4 ^ (r + 1) * (((n : ℝ) + 1) ^ r * (mzB β r * β 1) + β (r + 1))) := by
          gcongr
        push_cast
        calc _ = ∫ y, Tsum f n y ^ (2 * r + 2) ∂(Measure.pi fun _ : Fin n => ν) +
              4 ^ (r + 1) * ((∫ t, f t ^ 2 ∂ν) *
              ∫ y, Tsum f n y ^ (2 * r) ∂(Measure.pi fun _ : Fin n => ν) +
                ∫ t, f t ^ (2 * r + 2) ∂ν) := by ring
          _ ≤ n * (4 ^ (r + 1) * ((n : ℝ) ^ r * (mzB β r * β 1) + β (r + 1))) +
              4 ^ (r + 1) * ((n : ℝ) ^ r * (mzB β r * β 1) + β (r + 1)) := add_le_add ihn a1
          _ = ((n : ℝ) + 1) * (4 ^ (r + 1) * ((n : ℝ) ^ r * (mzB β r * β 1) + β (r + 1))) := by ring
          _ ≤ _ := a2
    have hnn : (n : ℝ) ≤ (n : ℝ) ^ (r + 1) := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp
      · exact le_self_pow₀ (by exact_mod_cast h) (by omega)
    rw [show 2 * (r + 1) = 2 * r + 2 by ring]
    refine (claim n).trans ?_
    simp only [mzB]
    have hY : (n : ℝ) * β (r + 1) ≤ (n : ℝ) ^ (r + 1) * β (r + 1) := mul_le_mul_of_nonneg_right hnn hbr
    calc (n : ℝ) * (4 ^ (r + 1) * ((n : ℝ) ^ r * (mzB β r * β 1) + β (r + 1)))
        = 4 ^ (r + 1) * ((n : ℝ) ^ (r + 1) * (mzB β r * β 1) + n * β (r + 1)) := by ring
      _ ≤ 4 ^ (r + 1) * ((n : ℝ) ^ (r + 1) * (mzB β r * β 1) + (n : ℝ) ^ (r + 1) * β (r + 1)) := by
          gcongr
      _ = _ := by ring

end sums

section transition

variable {σ : ℝ → ℝ}

lemma even_pow_add_le (a b : ℝ) (r : ℕ) :
    (a + b) ^ (2 * r) ≤ 2 ^ (2 * r) * (a ^ (2 * r) + b ^ (2 * r)) := by
  have ev := even_two_mul r
  have h1 : (a + b) ^ (2 * r) ≤ (|a| + |b|) ^ (2 * r) := by
    rw [← ev.pow_abs (a + b)]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_add_le a b) _
  have h2 := add_pow_le (abs_nonneg a) (abs_nonneg b) (2 * r)
  rw [ev.pow_abs, ev.pow_abs] at h2
  have h3 : (2:ℝ) ^ (2 * r - 1) ≤ 2 ^ (2 * r) := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  have h4 : 0 ≤ a ^ (2 * r) + b ^ (2 * r) := add_nonneg (ev.pow_nonneg a) (ev.pow_nonneg b)
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ _ := mul_le_mul_of_nonneg_right h3 h4

lemma int_poly1 {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → ℝ} (h1 : Integrable T μ) (a w : ℝ) :
    ∫ x, (a * T x + w) ∂μ = a * (∫ x, T x ∂μ) + w := by
  rw [integral_add (h1.const_mul a) (integrable_const w), integral_const_mul]; simp

lemma int_poly2 {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → ℝ} (h1 : Integrable T μ) (h2 : Integrable (fun x => T x ^ 2) μ) (a w : ℝ) :
    ∫ x, (a * T x + w) ^ 2 ∂μ =
      a ^ 2 * (∫ x, T x ^ 2 ∂μ) + 2 * a * w * (∫ x, T x ∂μ) + w ^ 2 := by
  have e : ∀ x, (a * T x + w) ^ 2 = (a ^ 2 * T x ^ 2 + 2 * a * w * T x) + w ^ 2 := fun x => by ring
  simp_rw [e]
  have i1 : Integrable (fun x => a ^ 2 * T x ^ 2 + 2 * a * w * T x) μ :=
    (h2.const_mul _).add (h1.const_mul _)
  rw [integral_add i1 (integrable_const _), integral_add (h2.const_mul _) (h1.const_mul _),
    integral_const_mul, integral_const_mul]
  simp

lemma int_poly3 {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → ℝ} (h1 : Integrable T μ) (h2 : Integrable (fun x => T x ^ 2) μ)
    (h3 : Integrable (fun x => T x ^ 3) μ) (a w : ℝ) :
    ∫ x, (a * T x + w) ^ 3 ∂μ = a ^ 3 * (∫ x, T x ^ 3 ∂μ) + 3 * a ^ 2 * w * (∫ x, T x ^ 2 ∂μ) +
      3 * a * w ^ 2 * (∫ x, T x ∂μ) + w ^ 3 := by
  have e : ∀ x, (a * T x + w) ^ 3 =
      ((a ^ 3 * T x ^ 3 + 3 * a ^ 2 * w * T x ^ 2) + 3 * a * w ^ 2 * T x) + w ^ 3 := fun x => by ring
  simp_rw [e]
  have i1 : Integrable (fun x => a ^ 3 * T x ^ 3 + 3 * a ^ 2 * w * T x ^ 2) μ :=
    (h3.const_mul _).add (h2.const_mul _)
  have i2 : Integrable (fun x => a ^ 3 * T x ^ 3 + 3 * a ^ 2 * w * T x ^ 2 + 3 * a * w ^ 2 * T x) μ :=
    i1.add (h1.const_mul _)
  rw [integral_add i2 (integrable_const _), integral_add i1 (h1.const_mul _),
    integral_add (h3.const_mul _) (h2.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul]
  simp

/-- `g(s) = ⟨σ²⟩_s`. -/
noncomputable def gS (σ : ℝ → ℝ) (s : ℝ) : ℝ := gaussAvg s (fun t => σ t ^ 2)

/-- third central moment of `σ²` under `N(0,s)`. -/
noncomputable def c3S (σ : ℝ → ℝ) (s : ℝ) : ℝ :=
  gaussAvg s (fun t => σ t ^ 6) - 3 * gS σ s * gaussAvg s (fun t => σ t ^ 4) + 2 * gS σ s ^ 3

/-- moment bounds for the centered `σ²`. -/
noncomputable def βS (σ : ℝ → ℝ) (s : ℝ) (j : ℕ) : ℝ :=
  2 ^ (2 * j) * (gaussAvg s (fun t => (σ t ^ 2) ^ (2 * j)) + gS σ s ^ (2 * j))

lemma PB_gS (hσ : PB σ) : PB (fun s => gS σ s) := PB.avg (hσ.pow 2)

lemma PB_v (hσ : PB σ) : PB (fun s => gaussVarSq σ s) :=
  (PB.avg (hσ.pow 4)).sub ((PB.avg (hσ.pow 2)).pow 2)

lemma PB_c3 (hσ : PB σ) : PB (fun s => c3S σ s) :=
  ((PB.avg (hσ.pow 6)).sub (((PB_gS hσ).const_mul 3).mul (PB.avg (hσ.pow 4)))).add
    (((PB_gS hσ).pow 3).const_mul 2)

lemma PB_βS (hσ : PB σ) (j : ℕ) : PB (fun s => βS σ s j) :=
  ((PB.avg ((hσ.pow 2).pow (2 * j))).add ((PB_gS hσ).pow (2 * j))).const_mul _

lemma PB_mzB (hσ : PB σ) : ∀ r, PB (fun s => mzB (βS σ s) r)
  | 0 => by simp only [mzB]; exact PB.const 1
  | r + 1 => by
    simp only [mzB]
    exact (((PB_mzB hσ r).mul (PB_βS hσ 1)).add (PB_βS hσ (r + 1))).const_mul _

lemma centered_integrable (hσ : PB σ) (s c : ℝ) (p : ℕ) :
    Integrable (fun t => (σ t ^ 2 - c) ^ p) (gaussianReal 0 s.toNNReal) :=
  (((hσ.pow 2).sub (PB.const c)).pow p).integrable _

lemma centered_mean (hσ : PB σ) (s : ℝ) :
    ∫ t, (σ t ^ 2 - gS σ s) ∂(gaussianReal 0 s.toNNReal) = 0 := by
  rw [integral_sub ((hσ.pow 2).integrable _) (integrable_const _)]
  simp [gS, gaussAvg]

lemma centered_sq (hσ : PB σ) (s : ℝ) :
    ∫ t, (σ t ^ 2 - gS σ s) ^ 2 ∂(gaussianReal 0 s.toNNReal) = gaussVarSq σ s := by
  have e : ∀ t, (σ t ^ 2 - gS σ s) ^ 2 = (σ t ^ 4 + (-2 * gS σ s) * σ t ^ 2) + gS σ s ^ 2 :=
    fun t => by ring
  simp_rw [e]
  have i4 := (hσ.pow 4).integrable s.toNNReal
  have i2 := (hσ.pow 2).integrable s.toNNReal
  have i1 : Integrable (fun t => σ t ^ 4 + (-2 * gS σ s) * σ t ^ 2) (gaussianReal 0 s.toNNReal) :=
    i4.add (i2.const_mul _)
  rw [integral_add i1 (integrable_const _), integral_add i4 (i2.const_mul _), integral_const_mul]
  simp only [gaussVarSq, gS, gaussAvg, integral_const, smul_eq_mul, probReal_univ, one_mul]
  ring

lemma centered_cube (hσ : PB σ) (s : ℝ) :
    ∫ t, (σ t ^ 2 - gS σ s) ^ 3 ∂(gaussianReal 0 s.toNNReal) = c3S σ s := by
  have e : ∀ t, (σ t ^ 2 - gS σ s) ^ 3 = ((σ t ^ 6 + (-3 * gS σ s) * σ t ^ 4) +
      (3 * gS σ s ^ 2) * σ t ^ 2) + (-(gS σ s ^ 3)) := fun t => by ring
  simp_rw [e]
  have i6 := (hσ.pow 6).integrable s.toNNReal
  have i4 := (hσ.pow 4).integrable s.toNNReal
  have i2 := (hσ.pow 2).integrable s.toNNReal
  have i1 : Integrable (fun t => σ t ^ 6 + (-3 * gS σ s) * σ t ^ 4) (gaussianReal 0 s.toNNReal) :=
    i6.add (i4.const_mul _)
  have i1' : Integrable (fun t => σ t ^ 6 + (-3 * gS σ s) * σ t ^ 4 + (3 * gS σ s ^ 2) * σ t ^ 2)
      (gaussianReal 0 s.toNNReal) := i1.add (i2.const_mul _)
  rw [integral_add i1' (integrable_const _), integral_add i1 (i2.const_mul _),
    integral_add i6 (i4.const_mul _), integral_const_mul, integral_const_mul]
  simp only [c3S, gS, gaussAvg, integral_const, smul_eq_mul, probReal_univ, one_mul]
  ring

lemma Q_eq (σ : ℝ → ℝ) (Cb CW K' s : ℝ) {n : ℕ} (hn : 1 ≤ n) (y : Fin n → ℝ) :
    Cb + CW / n * ∑ j, σ (y j) ^ 2 - K' =
      CW / n * Tsum (fun t => σ t ^ 2 - gS σ s) n y + (Cb + CW * gS σ s - K') := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  simp only [Tsum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp
  ring

theorem trans_mom1 (hσ : PB σ) (Cb CW K' s : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ∫ y, (Cb + CW / n * ∑ j, σ (y j) ^ 2 - K')
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 s.toNNReal) = Cb + CW * gS σ s - K' := by
  have hf := centered_integrable hσ s (gS σ s)
  have hT := integrable_Tsum_pow hf n
  simp_rw [Q_eq σ Cb CW K' s hn]
  rw [int_poly1 (by simpa using hT 1), Tsum_mean hf (centered_mean hσ s)]
  ring

theorem trans_mom2 (hσ : PB σ) (Cb CW K' s : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ∫ y, (Cb + CW / n * ∑ j, σ (y j) ^ 2 - K') ^ 2
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 s.toNNReal) =
      (Cb + CW * gS σ s - K') ^ 2 + CW ^ 2 / n * gaussVarSq σ s := by
  have hf := centered_integrable hσ s (gS σ s)
  have hT := integrable_Tsum_pow hf n
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  simp_rw [Q_eq σ Cb CW K' s hn]
  rw [int_poly2 (by simpa using hT 1) (hT 2), Tsum_mean hf (centered_mean hσ s),
    Tsum_sq hf (centered_mean hσ s), centered_sq hσ s]
  field_simp
  ring

theorem trans_mom3 (hσ : PB σ) (Cb CW K' s : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ∫ y, (Cb + CW / n * ∑ j, σ (y j) ^ 2 - K') ^ 3
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 s.toNNReal) =
      (Cb + CW * gS σ s - K') ^ 3 + 3 * CW ^ 2 / n * (Cb + CW * gS σ s - K') * gaussVarSq σ s +
        CW ^ 3 / n ^ 2 * c3S σ s := by
  have hf := centered_integrable hσ s (gS σ s)
  have hT := integrable_Tsum_pow hf n
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  simp_rw [Q_eq σ Cb CW K' s hn]
  rw [int_poly3 (by simpa using hT 1) (hT 2) (hT 3), Tsum_mean hf (centered_mean hσ s),
    Tsum_sq hf (centered_mean hσ s), Tsum_cube hf (centered_mean hσ s), centered_sq hσ s,
    centered_cube hσ s]
  field_simp
  ring

theorem trans_even (hσ : PB σ) (Cb CW K' s : ℝ) {n : ℕ} (hn : 1 ≤ n) (r : ℕ) :
    ∫ y, (Cb + CW / n * ∑ j, σ (y j) ^ 2 - K') ^ (2 * r)
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 s.toNNReal) ≤
      2 ^ (2 * r) * ((Cb + CW * gS σ s - K') ^ (2 * r) + CW ^ (2 * r) * mzB (βS σ s) r / n ^ r) := by
  have hf := centered_integrable hσ s (gS σ s)
  have hT := integrable_Tsum_pow hf n
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have ev := even_two_mul r
  have hβ0 : ∀ j, 0 ≤ βS σ s j := by
    intro j
    have ej := even_two_mul j
    have : 0 ≤ gaussAvg s (fun t => (σ t ^ 2) ^ (2 * j)) :=
      integral_nonneg fun t => ej.pow_nonneg _
    unfold βS; have := ej.pow_nonneg (gS σ s); positivity
  have hβ : ∀ j, ∫ t, (σ t ^ 2 - gS σ s) ^ (2 * j) ∂(gaussianReal 0 s.toNNReal) ≤ βS σ s j := by
    intro j
    have ej := even_two_mul j
    have iR : Integrable (fun t => 2 ^ (2 * j) * ((σ t ^ 2) ^ (2 * j) + gS σ s ^ (2 * j)))
        (gaussianReal 0 s.toNNReal) :=
      ((((hσ.pow 2).pow (2 * j)).integrable _).add (integrable_const _)).const_mul _
    refine (integral_mono (hf _) iR fun t => ?_).trans (le_of_eq ?_)
    · have := even_pow_add_le (σ t ^ 2) (-gS σ s) j
      rw [ej.neg_pow] at this
      simpa [sub_eq_add_neg] using this
    · rw [integral_const_mul, integral_add (((hσ.pow 2).pow (2 * j)).integrable _)
        (integrable_const _)]
      simp [βS, gaussAvg]
  have hmz := mz_bound hf (centered_mean hσ s) hβ0 hβ r n
  have hB := mzB_nonneg hβ0 r
  simp_rw [Q_eq σ Cb CW K' s hn]
  have iR : Integrable (fun y => 2 ^ (2 * r) * ((CW / n * Tsum (fun t => σ t ^ 2 - gS σ s) n y) ^ (2 * r) +
      (Cb + CW * gS σ s - K') ^ (2 * r)))
      (Measure.pi fun _ : Fin n => gaussianReal 0 s.toNNReal) := by
    have := ((hT (2 * r)).const_mul ((CW / n) ^ (2 * r))).add
      (integrable_const ((Cb + CW * gS σ s - K') ^ (2 * r)))
    refine (this.const_mul (2 ^ (2 * r))).congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply, mul_pow]
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => ev.pow_nonneg _) iR
    (Filter.Eventually.of_forall fun y => even_pow_add_le _ _ r)).trans ?_
  rw [integral_const_mul, integral_add ((hT (2 * r)).const_mul ((CW / n) ^ (2 * r)) |>.congr
    (Filter.Eventually.of_forall fun y => by simp only [mul_pow])) (integrable_const _)]
  simp only [mul_pow, integral_const_mul, integral_const, probReal_univ, smul_eq_mul, one_mul]
  have h2 : (0:ℝ) ≤ 2 ^ (2 * r) := by positivity
  apply mul_le_mul_of_nonneg_left _ h2
  have hc : (0:ℝ) ≤ (CW / n) ^ (2 * r) := ev.pow_nonneg _
  have key : (CW / n) ^ (2 * r) * ∫ y, Tsum (fun t => σ t ^ 2 - gS σ s) n y ^ (2 * r)
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 s.toNNReal) ≤
      CW ^ (2 * r) * mzB (βS σ s) r / n ^ r := by
    calc _ ≤ (CW / n) ^ (2 * r) * ((n : ℝ) ^ r * mzB (βS σ s) r) := mul_le_mul_of_nonneg_left hmz hc
      _ = CW ^ (2 * r) * mzB (βS σ s) r / n ^ r := by
          rw [div_pow]; field_simp; ring
  linarith

end transition

section netTrans

variable {n : ℕ → ℕ} {L : ℕ}

lemma act_succ (Cb CW : ℝ) (σ : ℝ → ℝ) (θ : Params n L) (x : Fin (n 0) → ℝ) (m : ℕ)
    (j : Fin (n (m + 1))) : act Cb CW σ θ x (m + 1) j = σ (mlpZ Cb CW σ θ x (m + 1) j) := by
  simp [act]

lemma Sv_zero (Cb CW : ℝ) (σ : ℝ → ℝ) (θ : Params n L) (x : Fin (n 0) → ℝ) :
    Sv Cb CW σ θ x 0 = Cb + CW / n 0 * ∑ j, x j ^ 2 := by
  simp only [Sv, act]
  rfl

/-- the one-step transition of the collective variance `S_m ↦ S_{m+1}`. -/
theorem trans_S {Cb CW : ℝ} (hCb : 0 ≤ Cb) (hCW : 0 ≤ CW) {σ : ℝ → ℝ} (hσ : PB σ)
    (x : Fin (n 0) → ℝ) (m : ℕ) (hm : m + 1 < L + 1) {Φ : ℝ → ℝ} (hΦ : PB Φ) :
    Integrable (fun θ => ∫ y, Φ (Cb + CW / n (m + 1) * ∑ j, σ (y j) ^ 2)
        ∂(Measure.pi fun _ : Fin (n (m + 1)) => gaussianReal 0 (Sv Cb CW σ θ x m).toNNReal))
      (stdGaussianParams n L) ∧
    ∫ θ, Φ (Sv Cb CW σ θ x (m + 1)) ∂(stdGaussianParams n L) =
      ∫ θ, (∫ y, Φ (Cb + CW / n (m + 1) * ∑ j, σ (y j) ^ 2)
        ∂(Measure.pi fun _ : Fin (n (m + 1)) => gaussianReal 0 (Sv Cb CW σ θ x m).toNNReal))
        ∂(stdGaussianParams n L) := by
  have hmeas : Measurable (fun y : Fin (n (m + 1)) → ℝ => Φ (Cb + CW / n (m + 1) * ∑ j, σ (y j) ^ 2)) :=
    hΦ.1.comp (measurable_const.add (measurable_const.mul
      (Finset.measurable_sum _ fun j _ => (hσ.1.comp (measurable_pi_apply j)).pow_const 2)))
  have e : ∀ θ : Params n L, Φ (Sv Cb CW σ θ x (m + 1)) =
      Φ (Cb + CW / n (m + 1) * ∑ j, σ (mlpZ Cb CW σ θ x (m + 1) j) ^ 2) := by
    intro θ; simp only [Sv, act_succ]
  have hint : Integrable (fun θ : Params n L =>
      Φ (Cb + CW / n (m + 1) * ∑ j, σ (mlpZ Cb CW σ θ x (m + 1) j) ^ 2)) (stdGaussianParams n L) := by
    refine (PT.integrable (PT.comp hΦ (PT_Sv Cb CW hσ x (m + 1)))).congr
      (Filter.Eventually.of_forall fun θ => ?_)
    exact e θ
  have h := condGauss_integral Cb CW hCb hCW σ x m (by omega)
    (Φ := fun y => Φ (Cb + CW / n (m + 1) * ∑ j, σ (y j) ^ 2)) hmeas hint
  refine ⟨h.1, ?_⟩
  simp only [e]
  exact h.2

end netTrans

section taylorGV

variable {σ : ℝ → ℝ}

lemma contDiff_gS (hσ : PB σ) : ContDiffOn ℝ 3 (fun s => gS σ s) (Set.Ioi 0) :=
  contDiffOn_gaussAvg 3 (hσ.pow 2)

lemma contDiff_v (hσ : PB σ) : ContDiffOn ℝ 3 (fun s => gaussVarSq σ s) (Set.Ioi 0) :=
  (contDiffOn_gaussAvg 3 (hσ.pow 4)).sub ((contDiffOn_gaussAvg 3 (hσ.pow 2)).pow 2)

/-- `g(s) = g(K) + g'(K)(s-K) + c₂(s-K)² + O(|s-K|³(1+(s-K)²)^q)` globally. -/
theorem g_T2 (hσ : PB σ) {K : ℝ} (hK : 0 < K) : ∃ c2 M : ℝ, ∃ q : ℕ, ∀ s,
    |gS σ s - gS σ K - deriv (gS σ) K * (s - K) - c2 * (s - K) ^ 2| ≤
      M * (|s - K| ^ 3 * (1 + (s - K) ^ 2) ^ q) :=
  taylor_global (PB_gS hσ) (contDiff_gS hσ) hK

/-- first-order expansion with quadratic remainder, from a second-order one. -/
theorem T1_of_T2 {F : ℝ → ℝ} {K d c2 M : ℝ} {q : ℕ}
    (h : ∀ s, |F s - F K - d * (s - K) - c2 * (s - K) ^ 2| ≤ M * (|s - K| ^ 3 * (1 + (s - K) ^ 2) ^ q)) :
    ∃ M' : ℝ, ∀ s, |F s - F K - d * (s - K)| ≤ M' * ((s - K) ^ 2 * (1 + (s - K) ^ 2) ^ (q + 1)) := by
  obtain ⟨M', h'⟩ := lower_order (F := fun s => F s - F K - d * (s - K)) (c := c2) (a := 2) (M := M)
    (q := q) (K := K) (fun s => h s)
  exact ⟨M', fun s => by have := h' s; rwa [sq_abs] at this⟩

/-- zeroth-order (Lipschitz-type) bound from a first-order one. -/
theorem T0_of_T1 {F : ℝ → ℝ} {K d M : ℝ} {q : ℕ}
    (h : ∀ s, |F s - F K - d * (s - K)| ≤ M * ((s - K) ^ 2 * (1 + (s - K) ^ 2) ^ q)) :
    ∃ M' : ℝ, ∀ s, |F s - F K| ≤ M' * (|s - K| * (1 + (s - K) ^ 2) ^ (q + 1)) := by
  obtain ⟨M', h'⟩ := lower_order (F := fun s => F s - F K) (c := d) (a := 1) (M := M)
    (q := q) (K := K) (fun s => by simpa [pow_one, sq_abs] using h s)
  exact ⟨M', fun s => by simpa [pow_one] using h' s⟩

theorem v_T1 (hσ : PB σ) {K : ℝ} (hK : 0 < K) : ∃ M : ℝ, ∃ q : ℕ, ∀ s,
    |gaussVarSq σ s - gaussVarSq σ K - deriv (fun s => gaussVarSq σ s) K * (s - K)| ≤
      M * ((s - K) ^ 2 * (1 + (s - K) ^ 2) ^ q) := by
  obtain ⟨c2, M, q, h⟩ := taylor_global (PB_v hσ) (contDiff_v hσ) hK
  obtain ⟨M', h'⟩ := T1_of_T2 (F := fun s => gaussVarSq σ s) h
  exact ⟨M', q + 1, h'⟩

end taylorGV

section bd

variable {W : Type*} (N : W → ℕ)

/-- `F w = O(N_w^{-k})`, uniformly in `w`. -/
def Bd (F : W → ℝ) (k : ℕ) : Prop := ∃ C : ℝ, ∀ w, |F w| ≤ C / (N w : ℝ) ^ k

variable {N}

lemma Bd.add {F G : W → ℝ} {k : ℕ} (hF : Bd N F k) (hG : Bd N G k) :
    Bd N (fun w => F w + G w) k := by
  obtain ⟨C1, h1⟩ := hF
  obtain ⟨C2, h2⟩ := hG
  exact ⟨C1 + C2, fun w => (abs_add_le _ _).trans (by rw [add_div]; exact add_le_add (h1 w) (h2 w))⟩

lemma Bd.const_mul {F : W → ℝ} {k : ℕ} (hF : Bd N F k) (c : ℝ) : Bd N (fun w => c * F w) k := by
  obtain ⟨C, h⟩ := hF
  exact ⟨|c| * C, fun w => by
    rw [abs_mul, mul_div_assoc]; exact mul_le_mul_of_nonneg_left (h w) (abs_nonneg c)⟩

lemma Bd.neg {F : W → ℝ} {k : ℕ} (hF : Bd N F k) : Bd N (fun w => -F w) k := by
  obtain ⟨C, h⟩ := hF
  exact ⟨C, fun w => by rw [abs_neg]; exact h w⟩

lemma Bd.sub {F G : W → ℝ} {k : ℕ} (hF : Bd N F k) (hG : Bd N G k) :
    Bd N (fun w => F w - G w) k := by
  simpa [sub_eq_add_neg] using hF.add hG.neg

lemma Bd.of_le {F G : W → ℝ} {k : ℕ} (hG : Bd N G k) (h : ∀ w, |F w| ≤ G w) : Bd N F k := by
  obtain ⟨C, hC⟩ := hG
  exact ⟨C, fun w => (h w).trans ((le_abs_self _).trans (hC w))⟩

lemma Bd.const (c : ℝ) : Bd N (fun _ => c) 0 := ⟨|c|, fun w => by simp⟩

lemma Bd.mono (hN : ∀ w, 1 ≤ N w) {F : W → ℝ} {k k' : ℕ} (hF : Bd N F k) (hk : k' ≤ k) :
    Bd N F k' := by
  obtain ⟨C, h⟩ := hF
  refine ⟨C, fun w => (h w).trans ?_⟩
  have hN1 : (1 : ℝ) ≤ N w := by exact_mod_cast hN w
  have hpos : (0 : ℝ) < (N w : ℝ) ^ k' := by positivity
  have hC : 0 ≤ C := by
    have := (abs_nonneg _).trans (h w)
    by_contra hc
    have : C / (N w : ℝ) ^ k < 0 := div_neg_of_neg_of_pos (not_le.1 hc) (by positivity)
    linarith
  exact div_le_div_of_nonneg_left hC hpos (pow_le_pow_right₀ hN1 hk)

lemma Bd.mul {F G : W → ℝ} {k1 k2 : ℕ} (hF : Bd N F k1) (hG : Bd N G k2) :
    Bd N (fun w => F w * G w) (k1 + k2) := by
  obtain ⟨C1, h1⟩ := hF
  obtain ⟨C2, h2⟩ := hG
  refine ⟨C1 * C2, fun w => ?_⟩
  rw [abs_mul, pow_add, ← div_mul_div_comm]
  exact mul_le_mul (h1 w) (h2 w) (abs_nonneg _) ((abs_nonneg _).trans (h1 w))

end bd

section kernelGlue

/-- M8: on the diagonal, the NNGP pair average is the one-variable average of `σ²`. -/
lemma gaussPairAvg_diag {σ : ℝ → ℝ} (hσ : Measurable σ) {K : ℝ} (hK : 0 < K) :
    gaussPairAvg σ K K K = gS σ K := by
  let A : Matrix (Fin 2) (Fin 1) ℝ := Matrix.of fun _ _ => Real.sqrt K
  have hAA : A * A.transpose = !![K, K; K, K] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A, Matrix.mul_apply, Real.mul_self_sqrt hK.le]
  have hmeas : Measurable (fun u : Fin 1 → ℝ => WithLp.toLp 2 (A.mulVec u)) :=
    ((PiLp.continuous_toLp 2 _).comp
      (Continuous.matrix_mulVec continuous_const continuous_id)).measurable
  have hF : Measurable (fun v : EuclideanSpace ℝ (Fin 2) => σ (v 0) * σ (v 1)) :=
    (hσ.comp (PiLp.continuous_apply 2 _ 0).measurable).mul
      (hσ.comp (PiLp.continuous_apply 2 _ 1).measurable)
  unfold gaussPairAvg
  rw [← hAA, ← map_pi_gaussian_linear A, integral_map hmeas.aemeasurable hF.aestronglyMeasurable]
  have e : ∀ u : Fin 1 → ℝ, σ ((WithLp.toLp 2 (A.mulVec u)) 0) * σ ((WithLp.toLp 2 (A.mulVec u)) 1) =
      σ (Real.sqrt K * u 0) ^ 2 := by
    intro u; simp [A, Matrix.mulVec, dotProduct, sq]
  simp_rw [e]
  rw [integral_comp_eval (μ := fun _ => gaussianReal 0 1) (i := 0)
    (f := fun t => σ (Real.sqrt K * t) ^ 2)
    ((hσ.comp (measurable_const.mul measurable_id)).pow_const 2).aestronglyMeasurable,
    gS, gaussAvg_scale hK (hσ.pow_const 2)]

end kernelGlue

section chainAlg

lemma abs_odd_le (d : ℝ) (k : ℕ) : |d| ^ (2 * k + 1) ≤ d ^ (2 * k) * (1 + d ^ 2) := by
  have h1 : |d| ≤ 1 + d ^ 2 := by nlinarith [abs_nonneg d, sq_abs d]
  rw [pow_succ, (even_two_mul k).pow_abs]
  exact mul_le_mul_of_nonneg_left h1 ((even_two_mul k).pow_nonneg d)

lemma weight_le (d : ℝ) (q : ℕ) : (1 + d ^ 2) ^ q ≤ 2 ^ q * (1 + d ^ (2 * q)) := by
  have h := add_pow_le zero_le_one (sq_nonneg d) q
  rw [one_pow, ← pow_mul] at h
  have h2 : (2:ℝ) ^ (q - 1) ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  have h3 : 0 ≤ 1 + d ^ (2 * q) := add_nonneg zero_le_one ((even_two_mul q).pow_nonneg d)
  exact h.trans (mul_le_mul_of_nonneg_right h2 h3)

lemma growth_shift (s K : ℝ) : 1 + |s| ≤ 2 * (1 + |K|) * (1 + (s - K) ^ 2) := by
  have h1 : |s| ≤ |K| + |s - K| := by
    calc |s| = |K + (s - K)| := by ring_nf
      _ ≤ |K| + |s - K| := abs_add_le _ _
  have h2 : |s - K| ≤ 1 + (s - K) ^ 2 := by nlinarith [abs_nonneg (s - K), sq_abs (s - K)]
  nlinarith [abs_nonneg K, sq_nonneg (s - K), abs_nonneg (s - K)]

end chainAlg

end FW
end LesHouchesWidth

/-! ## M6: abstract chain theorem (run 2) -/


namespace LesHouchesWidth
namespace FW

open MeasureTheory ProbabilityTheory

section ordAlg

/-- `f s = O(|s-K|^j)` with polynomial tails, and `f` measurable. -/
def Ord (K : ℝ) (j : ℕ) (f : ℝ → ℝ) : Prop :=
  Measurable f ∧ ∃ c : ℝ, ∃ q : ℕ, 0 ≤ c ∧ ∀ s, |f s| ≤ c * (|s - K| ^ j * (1 + (s - K) ^ 2) ^ q)

variable {K : ℝ}

lemma Ord.of_bound {f : ℝ → ℝ} {j q : ℕ} {c : ℝ} (hm : Measurable f)
    (h : ∀ s, |f s| ≤ c * (|s - K| ^ j * (1 + (s - K) ^ 2) ^ q)) : Ord K j f :=
  ⟨hm, |c|, q, abs_nonneg c, fun s => (h s).trans
    (mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity))⟩

lemma Ord.congr {f g : ℝ → ℝ} {j : ℕ} (h : Ord K j f) (e : ∀ s, g s = f s) : Ord K j g := by
  rw [show g = f from funext e]; exact h

lemma Ord.const (c : ℝ) : Ord K 0 (fun _ => c) :=
  Ord.of_bound (q := 0) (c := |c|) measurable_const fun s => by simp

lemma Ord.D : Ord K 1 (fun s => s - K) :=
  Ord.of_bound (q := 0) (c := 1) (measurable_id.sub_const K) fun s => by simp

lemma Ord.pb {f : ℝ → ℝ} (hf : PB f) : Ord K 0 f := by
  obtain ⟨hm, C, p, h⟩ := hf
  have hC := PB.nonneg_const h
  refine Ord.of_bound (q := p) (c := C * (2 * (1 + |K|)) ^ p) hm fun s => ?_
  have hg := growth_shift s K
  calc |f s| ≤ C * (1 + |s|) ^ p := h s
    _ ≤ C * (2 * (1 + |K|) * (1 + (s - K) ^ 2)) ^ p := by gcongr
    _ = _ := by rw [mul_pow]; ring

lemma Ord.add {f g : ℝ → ℝ} {j : ℕ} (hf : Ord K j f) (hg : Ord K j g) :
    Ord K j (fun s => f s + g s) := by
  obtain ⟨hmf, c1, q1, hc1, h1⟩ := hf
  obtain ⟨hmg, c2, q2, hc2, h2⟩ := hg
  refine ⟨hmf.add hmg, c1 + c2, q1 + q2, add_nonneg hc1 hc2, fun s => ?_⟩
  have hB : (1 : ℝ) ≤ 1 + (s - K) ^ 2 := by nlinarith [sq_nonneg (s - K)]
  have w1 : (1 + (s - K) ^ 2) ^ q1 ≤ (1 + (s - K) ^ 2) ^ (q1 + q2) :=
    pow_le_pow_right₀ hB (Nat.le_add_right _ _)
  have w2 : (1 + (s - K) ^ 2) ^ q2 ≤ (1 + (s - K) ^ 2) ^ (q1 + q2) :=
    pow_le_pow_right₀ hB (Nat.le_add_left _ _)
  have hA : 0 ≤ |s - K| ^ j := by positivity
  calc |f s + g s| ≤ |f s| + |g s| := abs_add_le _ _
    _ ≤ c1 * (|s - K| ^ j * (1 + (s - K) ^ 2) ^ q1) +
          c2 * (|s - K| ^ j * (1 + (s - K) ^ 2) ^ q2) := add_le_add (h1 s) (h2 s)
    _ ≤ c1 * (|s - K| ^ j * (1 + (s - K) ^ 2) ^ (q1 + q2)) +
          c2 * (|s - K| ^ j * (1 + (s - K) ^ 2) ^ (q1 + q2)) :=
        add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left w1 hA) hc1)
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left w2 hA) hc2)
    _ = _ := by ring

lemma Ord.const_mul {f : ℝ → ℝ} {j : ℕ} (hf : Ord K j f) (a : ℝ) :
    Ord K j (fun s => a * f s) := by
  obtain ⟨hm, c, q, hc, h⟩ := hf
  refine ⟨hm.const_mul a, |a| * c, q, by positivity, fun s => ?_⟩
  rw [abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h s) (abs_nonneg a)

lemma Ord.mul {f g : ℝ → ℝ} {j k : ℕ} (hf : Ord K j f) (hg : Ord K k g) :
    Ord K (j + k) (fun s => f s * g s) := by
  obtain ⟨hmf, c1, q1, hc1, h1⟩ := hf
  obtain ⟨hmg, c2, q2, hc2, h2⟩ := hg
  refine ⟨hmf.mul hmg, c1 * c2, q1 + q2, mul_nonneg hc1 hc2, fun s => ?_⟩
  rw [abs_mul]
  calc |f s| * |g s| ≤ (c1 * (|s - K| ^ j * (1 + (s - K) ^ 2) ^ q1)) *
        (c2 * (|s - K| ^ k * (1 + (s - K) ^ 2) ^ q2)) :=
      mul_le_mul (h1 s) (h2 s) (abs_nonneg _) (by positivity)
    _ = _ := by ring

lemma Ord.le {f : ℝ → ℝ} {j j' : ℕ} (hf : Ord K j f) (hj : j' ≤ j) : Ord K j' f := by
  obtain ⟨hm, c, q, hc, h⟩ := hf
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hj
  refine ⟨hm, c, q + m, hc, fun s => (h s).trans (mul_le_mul_of_nonneg_left ?_ hc)⟩
  have h1 : |s - K| ≤ 1 + (s - K) ^ 2 := by nlinarith [abs_nonneg (s - K), sq_abs (s - K)]
  have h2 : |s - K| ^ m ≤ (1 + (s - K) ^ 2) ^ m := pow_le_pow_left₀ (abs_nonneg _) h1 m
  have h3 : 0 ≤ |s - K| ^ j' * (1 + (s - K) ^ 2) ^ q := by positivity
  calc |s - K| ^ (j' + m) * (1 + (s - K) ^ 2) ^ q
      = |s - K| ^ j' * (1 + (s - K) ^ 2) ^ q * |s - K| ^ m := by ring
    _ ≤ |s - K| ^ j' * (1 + (s - K) ^ 2) ^ q * (1 + (s - K) ^ 2) ^ m :=
        mul_le_mul_of_nonneg_left h2 h3
    _ = _ := by ring

lemma Ord.pow {f : ℝ → ℝ} {j : ℕ} (hf : Ord K j f) : ∀ m : ℕ, Ord K (j * m) (fun s => f s ^ m)
  | 0 => (Ord.const 1).congr fun s => by simp
  | m + 1 => by
    rw [Nat.mul_succ]
    exact ((Ord.pow hf m).mul hf).congr fun s => by ring

lemma PB_wt (K : ℝ) (j q : ℕ) : PB (fun s => |s - K| ^ j * (1 + (s - K) ^ 2) ^ q) := by
  have hD : PB (fun s => s - K) := PB.id'.sub (PB.const K)
  have hA : PB (fun s => |s - K|) := by
    obtain ⟨hm, C, k, h⟩ := hD
    exact ⟨continuous_abs.measurable.comp hm, C, k, fun t => by simpa using h t⟩
  exact (hA.pow j).mul (((PB.const 1).add (hD.pow 2)).pow q)

lemma Ord.integrable {f : ℝ → ℝ} {j : ℕ} (hf : Ord K j f) {ν : Measure ℝ}
    (hI : ∀ F, PB F → Integrable F ν) : Integrable f ν := by
  obtain ⟨hm, c, q, hc, h⟩ := hf
  exact Integrable.mono' ((hI _ (PB_wt K j q)).const_mul c) hm.aestronglyMeasurable
    (ae_of_all _ fun s => by rw [Real.norm_eq_abs]; exact h s)

lemma gOrd {σ : ℝ → ℝ} (hσ : PB σ) (hK : 0 < K) : ∃ c2 : ℝ,
    Ord K 3 (fun s => gS σ s - gS σ K - deriv (gS σ) K * (s - K) - c2 * (s - K) ^ 2) ∧
    Ord K 2 (fun s => gS σ s - gS σ K - deriv (gS σ) K * (s - K)) ∧
    Ord K 1 (fun s => gS σ s - gS σ K) := by
  obtain ⟨c2, M, q, h⟩ := g_T2 hσ hK
  obtain ⟨M1, h1⟩ := T1_of_T2 h
  obtain ⟨M0, h0⟩ := T0_of_T1 h1
  have m1 : Measurable (fun s => gS σ s - gS σ K) := (PB_gS hσ).1.sub measurable_const
  have m2 : Measurable (fun s => gS σ s - gS σ K - deriv (gS σ) K * (s - K)) :=
    m1.sub (measurable_const.mul (measurable_id.sub_const K))
  exact ⟨c2, Ord.of_bound (c := M) (q := q)
      (m2.sub (measurable_const.mul ((measurable_id.sub_const K).pow_const 2))) h,
    Ord.of_bound (c := M1) (q := q + 1) m2 fun s => by rw [sq_abs]; exact h1 s,
    Ord.of_bound (c := M0) (q := q + 1 + 1) m1 fun s => by rw [pow_one]; exact h0 s⟩

lemma vOrd {σ : ℝ → ℝ} (hσ : PB σ) (hK : 0 < K) :
    Ord K 2 (fun s => gaussVarSq σ s - gaussVarSq σ K -
      deriv (fun s => gaussVarSq σ s) K * (s - K)) ∧
    Ord K 1 (fun s => gaussVarSq σ s - gaussVarSq σ K) := by
  obtain ⟨M, q, h⟩ := v_T1 hσ hK
  obtain ⟨M0, h0⟩ := T0_of_T1 h
  have m1 : Measurable (fun s => gaussVarSq σ s - gaussVarSq σ K) :=
    (PB_v hσ).1.sub measurable_const
  exact ⟨Ord.of_bound (c := M) (q := q) (m1.sub (measurable_const.mul (measurable_id.sub_const K)))
      fun s => by rw [sq_abs]; exact h s,
    Ord.of_bound (c := M0) (q := q + 1) m1 fun s => by rw [pow_one]; exact h0 s⟩

end ordAlg

section momBd

variable {W : Type*} {N : W → ℕ}

lemma Bd.congr {F G : W → ℝ} {k : ℕ} (hG : Bd N G k) (h : ∀ w, F w = G w) : Bd N F k := by
  rw [show F = G from funext h]; exact hG

lemma Bd.div_pow (hN : ∀ w, 1 ≤ N w) {M : W → ℕ} (hM : ∀ w, N w ≤ M w) (c : ℝ) (k : ℕ) :
    Bd N (fun w => c / (M w : ℝ) ^ k) k := by
  refine ⟨|c|, fun w => ?_⟩
  have h1 : (0 : ℝ) < N w := Nat.cast_pos.2 (hN w)
  have h2 : (N w : ℝ) ≤ M w := Nat.cast_le.2 (hM w)
  rw [abs_div, abs_of_pos (pow_pos (h1.trans_le h2) k)]
  exact div_le_div_of_nonneg_left (abs_nonneg c) (pow_pos h1 k) (pow_le_pow_left₀ h1.le h2 k)

/-- weighted centred moment bounds of a family of laws. -/
def Mom (N : W → ℕ) (ν : W → Measure ℝ) (K : ℝ) : Prop :=
  ∀ r q : ℕ, Bd N (fun w => ∫ s, |s - K| ^ (2 * r) * (1 + (s - K) ^ 2) ^ q ∂(ν w)) r

lemma dom {ν : W → Measure ℝ} {K : ℝ} (hM : Mom N ν K)
    (hI : ∀ w F, PB F → Integrable F (ν w)) {f : ℝ → ℝ} {r : ℕ} (hf : Ord K (2 * r) f) :
    Bd N (fun w => ∫ s, f s ∂(ν w)) r := by
  obtain ⟨_, c, q, hc, h⟩ := hf
  obtain ⟨C, hC⟩ := hM r q
  refine ⟨c * C, fun w => ?_⟩
  have i1 := (hI w _ (PB_wt K (2 * r) q)).const_mul c
  have h1 := norm_integral_le_of_norm_le (f := f) i1
    (ae_of_all _ fun s => by rw [Real.norm_eq_abs]; exact h s)
  rw [Real.norm_eq_abs, integral_const_mul] at h1
  calc _ ≤ _ := h1
    _ ≤ c * (C / (N w : ℝ) ^ r) := mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hC w)) hc
    _ = c * C / (N w : ℝ) ^ r := by ring

lemma mom_of_pure (hN : ∀ w, 1 ≤ N w) {ν : W → Measure ℝ} {K : ℝ}
    (hI : ∀ w F, PB F → Integrable F (ν w))
    (hp : ∀ k, Bd N (fun w => ∫ s, (s - K) ^ (2 * k) ∂(ν w)) k) : Mom N ν K := by
  intro r q
  have hB : Bd N (fun w => 2 ^ q * (∫ s, (s - K) ^ (2 * r) ∂(ν w) +
      ∫ s, (s - K) ^ (2 * (r + q)) ∂(ν w))) r :=
    ((hp r).add ((hp (r + q)).mono hN (Nat.le_add_right r q))).const_mul _
  refine hB.of_le fun w => ?_
  have hD : PB (fun s => s - K) := PB.id'.sub (PB.const K)
  have i1 := hI w _ (hD.pow (2 * r))
  have i2 := hI w _ (hD.pow (2 * (r + q)))
  have i3 := hI w _ (PB_wt K (2 * r) q)
  have i4 : Integrable (fun s => 2 ^ q * ((s - K) ^ (2 * r) + (s - K) ^ (2 * (r + q)))) (ν w) :=
    (i1.add i2).const_mul _
  have hnn : 0 ≤ ∫ s, |s - K| ^ (2 * r) * (1 + (s - K) ^ 2) ^ q ∂(ν w) :=
    integral_nonneg fun s => by positivity
  rw [abs_of_nonneg hnn, ← integral_add i1 i2, ← integral_const_mul]
  refine integral_mono i3 i4 fun s => ?_
  have := weight_le (s - K) q
  simp only
  rw [(even_two_mul r).pow_abs]
  calc (s - K) ^ (2 * r) * (1 + (s - K) ^ 2) ^ q
      ≤ (s - K) ^ (2 * r) * (2 ^ q * (1 + (s - K) ^ (2 * q))) :=
        mul_le_mul_of_nonneg_left this ((even_two_mul r).pow_nonneg _)
    _ = _ := by ring

end momBd

section intSplit

lemma int_split {ν : Measure ℝ} {F f g : ℝ → ℝ} (hf : Integrable f ν) (hg : Integrable g ν)
    (a : ℝ) (h : ∀ s, F s = f s + a * g s) :
    ∫ s, F s ∂ν = ∫ s, f s ∂ν + a * ∫ s, g s ∂ν := by
  rw [show F = fun s => f s + a * g s from funext h, integral_add hf (hg.const_mul a),
    integral_const_mul]

lemma int_split3 {ν : Measure ℝ} {F f g k : ℝ → ℝ} (hf : Integrable f ν) (hg : Integrable g ν)
    (hk : Integrable k ν) (a b : ℝ) (h : ∀ s, F s = f s + a * g s + b * k s) :
    ∫ s, F s ∂ν = ∫ s, f s ∂ν + a * ∫ s, g s ∂ν + b * ∫ s, k s ∂ν := by
  have i : Integrable (fun s => f s + a * g s) ν := hf.add (hg.const_mul a)
  have e1 := int_split i hk b h
  have e2 : ∫ s, (f s + a * g s) ∂ν = ∫ s, f s ∂ν + a * ∫ s, g s ∂ν :=
    int_split hf hg a fun s => rfl
  rw [e1, e2]

/-- variance of a law on `ℝ`. -/
noncomputable def var2 (ν : Measure ℝ) : ℝ := ∫ x, x ^ 2 ∂ν - (∫ x, x ∂ν) ^ 2

lemma var2_center {ν : Measure ℝ} [IsProbabilityMeasure ν] (hI : ∀ F, PB F → Integrable F ν)
    (K : ℝ) : var2 ν = ∫ x, (x - K) ^ 2 ∂ν - (∫ x, (x - K) ∂ν) ^ 2 := by
  have i2 := hI _ (PB.id'.pow 2)
  have i1 := hI _ PB.id'
  have i0 := hI _ (PB.const 1)
  have e1 : ∫ x, (x - K) ^ 2 ∂ν = ∫ x, x ^ 2 ∂ν + (-2 * K) * ∫ x, x ∂ν + K ^ 2 * ∫ _, (1:ℝ) ∂ν :=
    int_split3 i2 i1 i0 _ _ fun x => by ring
  have e2 : ∫ x, (x - K) ∂ν = ∫ x, x ∂ν + (-K) * ∫ _, (1:ℝ) ∂ν :=
    int_split i1 i0 _ fun x => by ring
  have e0 : ∫ _, (1:ℝ) ∂ν = 1 := by simp
  unfold var2
  rw [e1, e2, e0]
  ring

end intSplit

section chain

/-- abstract hypotheses on the layer laws `μ w ℓ` of the collective variance `S_ℓ`. -/
structure Chain {W : Type*} (N : W → ℕ) (nn : W → ℕ → ℕ) (μ : W → ℕ → Measure ℝ) (K : ℕ → ℝ)
    (L : ℕ) (Cb CW : ℝ) (σ : ℝ → ℝ) : Prop where
  hN : ∀ w, 1 ≤ N w
  hn : ∀ w ℓ, 1 ≤ ℓ → ℓ ≤ L → N w ≤ nn w ℓ
  hP : ∀ w ℓ, IsProbabilityMeasure (μ w ℓ)
  hI : ∀ w ℓ, ℓ ≤ L → ∀ F, PB F → Integrable F (μ w ℓ)
  h0 : ∀ w (F : ℝ → ℝ), ∫ x, F x ∂(μ w 0) = F (K 1)
  hKs : ∀ ℓ, ℓ + 1 ≤ L → K (ℓ + 2) = Cb + CW * gS σ (K (ℓ + 1))
  hKp : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ L → 0 < K ℓ
  hσ : PB σ
  t1 : ∀ w ℓ, ℓ + 1 ≤ L → ∫ x, (x - K (ℓ + 2)) ∂(μ w (ℓ + 1)) =
    ∫ s, (Cb + CW * gS σ s - K (ℓ + 2)) ∂(μ w ℓ)
  t2 : ∀ w ℓ, ℓ + 1 ≤ L → ∫ x, (x - K (ℓ + 2)) ^ 2 ∂(μ w (ℓ + 1)) =
    ∫ s, ((Cb + CW * gS σ s - K (ℓ + 2)) ^ 2 + CW ^ 2 / nn w (ℓ + 1) * gaussVarSq σ s) ∂(μ w ℓ)
  t3 : ∀ w ℓ, ℓ + 1 ≤ L → ∫ x, (x - K (ℓ + 2)) ^ 3 ∂(μ w (ℓ + 1)) =
    ∫ s, ((Cb + CW * gS σ s - K (ℓ + 2)) ^ 3 +
      3 * CW ^ 2 / nn w (ℓ + 1) * (Cb + CW * gS σ s - K (ℓ + 2)) * gaussVarSq σ s +
      CW ^ 3 / (nn w (ℓ + 1)) ^ 2 * c3S σ s) ∂(μ w ℓ)
  te : ∀ w ℓ r, ℓ + 1 ≤ L → ∫ x, (x - K (ℓ + 2)) ^ (2 * r) ∂(μ w (ℓ + 1)) ≤
    ∫ s, 2 ^ (2 * r) * ((Cb + CW * gS σ s - K (ℓ + 2)) ^ (2 * r) +
      CW ^ (2 * r) * mzB (βS σ s) r / (nn w (ℓ + 1)) ^ r) ∂(μ w ℓ)

/-- the induction invariant at level `ℓ`. -/
def ChainInv {W : Type*} (N : W → ℕ) (μ : W → ℕ → Measure ℝ) (K : ℕ → ℝ) (ℓ : ℕ) : Prop :=
  Mom N (fun w => μ w ℓ) (K (ℓ + 1)) ∧
  Bd N (fun w => ∫ s, (s - K (ℓ + 1)) ∂(μ w ℓ)) 1 ∧
  Bd N (fun w => ∫ s, (s - K (ℓ + 1)) ^ 3 ∂(μ w ℓ)) 2

namespace Chain

variable {W : Type*} {N : W → ℕ} {nn : W → ℕ → ℕ} {μ : W → ℕ → Measure ℝ} {K : ℕ → ℝ} {L : ℕ}
  {Cb CW : ℝ} {σ : ℝ → ℝ}

lemma inv_zero (hc : Chain N nn μ K L Cb CW σ) : ChainInv N μ K 0 := by
  refine ⟨fun r q => ⟨1, fun w => ?_⟩, ⟨0, fun w => ?_⟩, ⟨0, fun w => ?_⟩⟩
  · beta_reduce
    rw [hc.h0]
    simp only [zero_add, sub_self, abs_zero]
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp
    · rw [zero_pow (by omega)]
      simp only [zero_mul, abs_zero]
      positivity
  · beta_reduce; rw [hc.h0]; simp
  · beta_reduce; rw [hc.h0]; simp

lemma w_ord (hc : Chain N nn μ K L Cb CW σ) {ℓ : ℕ} (hℓ : ℓ + 1 ≤ L) : ∃ c2 : ℝ,
    Ord (K (ℓ + 1)) 1 (fun s => Cb + CW * gS σ s - K (ℓ + 2)) ∧
    Ord (K (ℓ + 1)) 2 (fun s => Cb + CW * gS σ s - K (ℓ + 2) -
      CW * deriv (gS σ) (K (ℓ + 1)) * (s - K (ℓ + 1))) ∧
    Ord (K (ℓ + 1)) 4 (fun s => (Cb + CW * gS σ s - K (ℓ + 2)) ^ 2 -
      (CW * deriv (gS σ) (K (ℓ + 1))) ^ 2 * (s - K (ℓ + 1)) ^ 2 -
      2 * CW ^ 2 * deriv (gS σ) (K (ℓ + 1)) * c2 * (s - K (ℓ + 1)) ^ 3) := by
  obtain ⟨c2, g3, g2, g1⟩ := gOrd hc.hσ (hc.hKp (ℓ + 1) (by omega) hℓ)
  have hKs := hc.hKs ℓ hℓ
  have hb : Ord (K (ℓ + 1)) 2 (fun s => Cb + CW * gS σ s - K (ℓ + 2) -
      CW * deriv (gS σ) (K (ℓ + 1)) * (s - K (ℓ + 1))) :=
    (g2.const_mul CW).congr fun s => by rw [hKs]; ring
  refine ⟨c2, (g1.const_mul CW).congr fun s => by rw [hKs]; ring, hb, ?_⟩
  exact (((Ord.D.mul g3).const_mul (2 * CW ^ 2 * deriv (gS σ) (K (ℓ + 1)))).add
    (hb.mul hb)).congr fun s => by rw [hKs]; ring

lemma mean_w (hc : Chain N nn μ K L Cb CW σ) {ℓ : ℕ} (hℓ : ℓ + 1 ≤ L)
    (hM : Mom N (fun w => μ w ℓ) (K (ℓ + 1)))
    (hA : Bd N (fun w => ∫ s, (s - K (ℓ + 1)) ∂(μ w ℓ)) 1) :
    Bd N (fun w => ∫ s, (Cb + CW * gS σ s - K (ℓ + 2)) ∂(μ w ℓ)) 1 := by
  obtain ⟨c2, hw, hb, -⟩ := hc.w_ord hℓ
  have hI : ∀ w F, PB F → Integrable F (μ w ℓ) := fun w => hc.hI w ℓ (by omega)
  refine ((dom hM hI (r := 1) hb).add
    (hA.const_mul (CW * deriv (gS σ) (K (ℓ + 1))))).congr fun w => ?_
  exact int_split (hb.integrable (hI w)) (Ord.D.integrable (hI w)) _ fun s => by ring

lemma inv_succ (hc : Chain N nn μ K L Cb CW σ) {ℓ : ℕ} (hℓ : ℓ + 1 ≤ L)
    (ih : ChainInv N μ K ℓ) : ChainInv N μ K (ℓ + 1) := by
  show Mom N (fun w => μ w (ℓ + 1)) (K (ℓ + 2)) ∧
    Bd N (fun w => ∫ s, (s - K (ℓ + 2)) ∂(μ w (ℓ + 1))) 1 ∧
    Bd N (fun w => ∫ s, (s - K (ℓ + 2)) ^ 3 ∂(μ w (ℓ + 1))) 2
  obtain ⟨hM, hA, hC⟩ := ih
  obtain ⟨c2, hw, hb, -⟩ := hc.w_ord hℓ
  obtain ⟨-, hv1⟩ := vOrd hc.hσ (hc.hKp (ℓ + 1) (by omega) hℓ)
  have hI : ∀ w F, PB F → Integrable F (μ w ℓ) := fun w => hc.hI w ℓ (by omega)
  have hI' : ∀ w F, PB F → Integrable F (μ w (ℓ + 1)) := fun w => hc.hI w (ℓ + 1) hℓ
  have hnn : ∀ w, N w ≤ nn w (ℓ + 1) := fun w => hc.hn w (ℓ + 1) (by omega) hℓ
  have hmw := hc.mean_w hℓ hM hA
  have hp : ∀ k, Bd N (fun w => ∫ s, (s - K (ℓ + 2)) ^ (2 * k) ∂(μ w (ℓ + 1))) k := by
    intro k
    have hwk : Ord (K (ℓ + 1)) (2 * k)
        (fun s => 2 ^ (2 * k) * (Cb + CW * gS σ s - K (ℓ + 2)) ^ (2 * k)) :=
      ((hw.pow (2 * k)).const_mul _).le (by omega)
    have hz : Ord (K (ℓ + 1)) 0 (fun s => mzB (βS σ s) k) := Ord.pb (PB_mzB hc.hσ k)
    refine ((dom hM hI hwk).add ((Bd.div_pow hc.hN hnn (2 ^ (2 * k) * CW ^ (2 * k)) k).mul
      (dom hM hI (r := 0) hz))).of_le fun w => ?_
    have h0 : 0 ≤ ∫ s, (s - K (ℓ + 2)) ^ (2 * k) ∂(μ w (ℓ + 1)) :=
      integral_nonneg fun s => (even_two_mul k).pow_nonneg _
    rw [abs_of_nonneg h0]
    refine (hc.te w ℓ k hℓ).trans (le_of_eq ?_)
    exact int_split (hwk.integrable (hI w)) (hz.integrable (hI w)) _ fun s => by ring
  refine ⟨mom_of_pure hc.hN hI' hp, hmw.congr fun w => hc.t1 w ℓ hℓ, ?_⟩
  have ha : Ord (K (ℓ + 1)) 1 (fun s => CW * deriv (gS σ) (K (ℓ + 1)) * (s - K (ℓ + 1))) :=
    Ord.D.const_mul _
  have hcube : Ord (K (ℓ + 1)) 4 (fun s => (Cb + CW * gS σ s - K (ℓ + 2)) ^ 3 -
      (CW * deriv (gS σ) (K (ℓ + 1))) ^ 3 * (s - K (ℓ + 1)) ^ 3) :=
    (hb.mul ((((ha.mul ha).const_mul 3).add (((ha.mul hb).le (by norm_num)).const_mul 3)).add
      ((hb.mul hb).le (by norm_num)))).congr fun s => by ring
  have hwv : Ord (K (ℓ + 1)) 2 (fun s => (Cb + CW * gS σ s - K (ℓ + 2)) *
      (gaussVarSq σ s - gaussVarSq σ (K (ℓ + 1)))) := hw.mul hv1
  have hc3 : Ord (K (ℓ + 1)) 0 (fun s => c3S σ s) := Ord.pb (PB_c3 hc.hσ)
  have hvv : Ord (K (ℓ + 1)) 0 (fun s => gaussVarSq σ s) := Ord.pb (PB_v hc.hσ)
  have B1 : Bd N (fun w => ∫ s, (Cb + CW * gS σ s - K (ℓ + 2)) ^ 3 ∂(μ w ℓ)) 2 :=
    ((dom hM hI (r := 2) hcube).add
      (hC.const_mul ((CW * deriv (gS σ) (K (ℓ + 1))) ^ 3))).congr fun w =>
      int_split (hcube.integrable (hI w)) ((Ord.D.pow 3).integrable (hI w)) _ fun s => by ring
  have B2 : Bd N (fun w => ∫ s, (Cb + CW * gS σ s - K (ℓ + 2)) * gaussVarSq σ s ∂(μ w ℓ)) 1 :=
    ((dom hM hI (r := 1) hwv).add (hmw.const_mul (gaussVarSq σ (K (ℓ + 1))))).congr fun w =>
      int_split (hwv.integrable (hI w)) (hw.integrable (hI w)) _ fun s => by ring
  have B3 : Bd N (fun w => ∫ s, c3S σ s ∂(μ w ℓ)) 0 := dom hM hI (r := 0) hc3
  refine ((B1.add ((Bd.div_pow hc.hN hnn (3 * CW ^ 2) 1).mul B2)).add
    ((Bd.div_pow hc.hN hnn (CW ^ 3) 2).mul B3)).congr fun w => ?_
  have e := int_split3 (ν := μ w ℓ) ((hw.pow 3).integrable (hI w)) ((hw.mul hvv).integrable (hI w))
    (hc3.integrable (hI w)) (3 * CW ^ 2 / nn w (ℓ + 1)) (CW ^ 3 / (nn w (ℓ + 1) : ℝ) ^ 2)
    (F := fun s => (Cb + CW * gS σ s - K (ℓ + 2)) ^ 3 +
      3 * CW ^ 2 / nn w (ℓ + 1) * (Cb + CW * gS σ s - K (ℓ + 2)) * gaussVarSq σ s +
      CW ^ 3 / (nn w (ℓ + 1)) ^ 2 * c3S σ s) fun s => by ring
  rw [hc.t3 w ℓ hℓ, e]
  ring

theorem inv (hc : Chain N nn μ K L Cb CW σ) : ∀ {ℓ : ℕ}, ℓ ≤ L → ChainInv N μ K ℓ
  | 0, _ => hc.inv_zero
  | ℓ + 1, h => hc.inv_succ h (hc.inv (by omega))

theorem P1 (hc : Chain N nn μ K L Cb CW σ) {ℓ : ℕ} (hℓ : ℓ ≤ L) :
    Bd N (fun w => var2 (μ w ℓ)) 1 := by
  obtain ⟨hM, hA, -⟩ := hc.inv hℓ
  have hI : ∀ w F, PB F → Integrable F (μ w ℓ) := fun w => hc.hI w ℓ hℓ
  have h2 : Bd N (fun w => ∫ s, (s - K (ℓ + 1)) ^ 2 ∂(μ w ℓ)) 1 :=
    dom hM hI (r := 1) ((Ord.D.pow 2).le (by norm_num))
  refine (h2.sub ((hA.mul hA).mono hc.hN (by norm_num))).congr fun w => ?_
  have := hc.hP w ℓ
  rw [var2_center (hI w) (K (ℓ + 1))]
  ring

theorem P2 (hc : Chain N nn μ K L Cb CW σ) {ℓ : ℕ} (hℓ : ℓ + 1 ≤ L) :
    Bd N (fun w => var2 (μ w (ℓ + 1)) - CW ^ 2 / nn w (ℓ + 1) * gaussVarSq σ (K (ℓ + 1)) -
      (CW * deriv (gS σ) (K (ℓ + 1))) ^ 2 * var2 (μ w ℓ)) 2 := by
  obtain ⟨hM, hA, hC⟩ := hc.inv (ℓ := ℓ) (by omega)
  obtain ⟨c2, hw, hb, hrem⟩ := hc.w_ord hℓ
  obtain ⟨hv2, -⟩ := vOrd hc.hσ (hc.hKp (ℓ + 1) (by omega) hℓ)
  have hI : ∀ w F, PB F → Integrable F (μ w ℓ) := fun w => hc.hI w ℓ (by omega)
  have hI' : ∀ w F, PB F → Integrable F (μ w (ℓ + 1)) := fun w => hc.hI w (ℓ + 1) hℓ
  have hnn : ∀ w, N w ≤ nn w (ℓ + 1) := fun w => hc.hn w (ℓ + 1) (by omega) hℓ
  have hmw := hc.mean_w hℓ hM hA
  have hD : Ord (K (ℓ + 1)) 1 (fun s => s - K (ℓ + 1)) := Ord.D
  have B1 := dom hM hI (r := 2) hrem
  have B2 := hC.const_mul (2 * CW ^ 2 * deriv (gS σ) (K (ℓ + 1)) * c2)
  have B3 := (Bd.div_pow hc.hN hnn (CW ^ 2) 1).mul (dom hM hI (r := 1) hv2)
  have B4 := (Bd.div_pow hc.hN hnn (CW ^ 2 * deriv (fun s => gaussVarSq σ s) (K (ℓ + 1))) 1).mul hA
  have B5 := hmw.mul hmw
  have B6 := (hA.mul hA).const_mul ((CW * deriv (gS σ) (K (ℓ + 1))) ^ 2)
  refine (((((B1.add B2).add B3).add B4).sub B5).add B6).congr fun w => ?_
  have := hc.hP w ℓ
  have := hc.hP w (ℓ + 1)
  have e1 := var2_center (hI' w) (K (ℓ + 2))
  have e2 := var2_center (hI w) (K (ℓ + 1))
  have e3 : ∫ s, ((Cb + CW * gS σ s - K (ℓ + 2)) ^ 2 + CW ^ 2 / nn w (ℓ + 1) * gaussVarSq σ s)
      ∂(μ w ℓ) = ∫ s, (Cb + CW * gS σ s - K (ℓ + 2)) ^ 2 ∂(μ w ℓ) +
        CW ^ 2 / nn w (ℓ + 1) * ∫ s, gaussVarSq σ s ∂(μ w ℓ) :=
    int_split ((hw.pow 2).integrable (hI w))
      ((Ord.pb (K := K (ℓ + 1)) (PB_v hc.hσ)).integrable (hI w)) _ fun s => rfl
  have e4 : ∫ s, (Cb + CW * gS σ s - K (ℓ + 2)) ^ 2 ∂(μ w ℓ) =
      ∫ s, ((Cb + CW * gS σ s - K (ℓ + 2)) ^ 2 -
        (CW * deriv (gS σ) (K (ℓ + 1))) ^ 2 * (s - K (ℓ + 1)) ^ 2 -
        2 * CW ^ 2 * deriv (gS σ) (K (ℓ + 1)) * c2 * (s - K (ℓ + 1)) ^ 3) ∂(μ w ℓ) +
      (CW * deriv (gS σ) (K (ℓ + 1))) ^ 2 * ∫ s, (s - K (ℓ + 1)) ^ 2 ∂(μ w ℓ) +
      (2 * CW ^ 2 * deriv (gS σ) (K (ℓ + 1)) * c2) * ∫ s, (s - K (ℓ + 1)) ^ 3 ∂(μ w ℓ) :=
    int_split3 (hrem.integrable (hI w)) ((hD.pow 2).integrable (hI w))
      ((hD.pow 3).integrable (hI w)) _ _ fun s => by ring
  have e5 : ∫ s, gaussVarSq σ s ∂(μ w ℓ) =
      ∫ s, (gaussVarSq σ s - gaussVarSq σ (K (ℓ + 1)) -
        deriv (fun s => gaussVarSq σ s) (K (ℓ + 1)) * (s - K (ℓ + 1))) ∂(μ w ℓ) +
      deriv (fun s => gaussVarSq σ s) (K (ℓ + 1)) * ∫ s, (s - K (ℓ + 1)) ∂(μ w ℓ) +
      gaussVarSq σ (K (ℓ + 1)) * ∫ _, (1 : ℝ) ∂(μ w ℓ) :=
    int_split3 (hv2.integrable (hI w)) (hD.integrable (hI w))
      ((Ord.const (K := K (ℓ + 1)) 1).integrable (hI w)) _ _ fun s => by ring
  have e6 : ∫ _, (1 : ℝ) ∂(μ w ℓ) = 1 := by simp
  rw [e1, e2, hc.t2 w ℓ hℓ, hc.t1 w ℓ hℓ, e3, e4, e5, e6]
  ring

end Chain

end chain

end FW
end LesHouchesWidth

/-! ## M8b + M9: network instance and final assembly (run 2) -/


namespace LesHouchesWidth
namespace FW

open MeasureTheory ProbabilityTheory

section inst

lemma PB.congr {f g : ℝ → ℝ} (hf : PB f) (h : ∀ t, g t = f t) : PB g := by
  rw [show g = f from funext h]; exact hf

/-- the admissible width profiles: the index set of the chain. -/
structure Net (n0 L : ℕ) where
  N : ℕ
  n : ℕ → ℕ
  h0 : n 0 = n0
  hN : 1 ≤ N
  hn : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ L → N ≤ n ℓ

variable {n0 L : ℕ}

/-- the law of `S_ℓ` for the width profile `w`. -/
noncomputable def netLaw (Cb CW : ℝ) (σ : ℝ → ℝ) (x : Fin n0 → ℝ) (w : Net n0 L) (ℓ : ℕ) :
    Measure ℝ :=
  (stdGaussianParams w.n L).map (fun θ => Sv Cb CW σ θ (x ∘ Fin.cast w.h0) ℓ)

variable {Cb CW : ℝ} {σ : ℝ → ℝ}

lemma netLaw_int (hσ : PB σ) (x : Fin n0 → ℝ) (w : Net n0 L) (ℓ : ℕ) {F : ℝ → ℝ} (hF : PB F) :
    Integrable F (netLaw Cb CW σ x w ℓ) :=
  (integrable_map_measure hF.1.aestronglyMeasurable (PT_Sv Cb CW hσ _ ℓ).1.aemeasurable).2
    (PT.integrable (PT.comp hF (PT_Sv Cb CW hσ _ ℓ)))

lemma netLaw_trans (hCb : 0 ≤ Cb) (hCW : 0 ≤ CW) (hσ : PB σ) (x : Fin n0 → ℝ) (w : Net n0 L)
    {m : ℕ} (hm : m + 1 ≤ L) {Φ G : ℝ → ℝ} (hΦ : PB Φ) (hG : PB G)
    (h : ∀ s, ∫ y, Φ (Cb + CW / w.n (m + 1) * ∑ j, σ (y j) ^ 2)
      ∂(Measure.pi fun _ : Fin (w.n (m + 1)) => gaussianReal 0 s.toNNReal) ≤ G s) :
    ∫ z, Φ z ∂(netLaw Cb CW σ x w (m + 1)) ≤ ∫ s, G s ∂(netLaw Cb CW σ x w m) := by
  have hT := trans_S (L := L) hCb hCW hσ (x ∘ Fin.cast w.h0) m (by omega) hΦ
  unfold netLaw
  rw [integral_map (PT_Sv Cb CW hσ _ (m + 1)).1.aemeasurable hΦ.1.aestronglyMeasurable,
    integral_map (PT_Sv Cb CW hσ _ m).1.aemeasurable hG.1.aestronglyMeasurable, hT.2]
  exact integral_mono hT.1 (PT.integrable (PT.comp hG (PT_Sv Cb CW hσ _ m))) fun θ => h _

lemma netLaw_trans_eq (hCb : 0 ≤ Cb) (hCW : 0 ≤ CW) (hσ : PB σ) (x : Fin n0 → ℝ)
    (w : Net n0 L) {m : ℕ} (hm : m + 1 ≤ L) {Φ G : ℝ → ℝ} (hΦ : PB Φ) (hG : Measurable G)
    (h : ∀ s, ∫ y, Φ (Cb + CW / w.n (m + 1) * ∑ j, σ (y j) ^ 2)
      ∂(Measure.pi fun _ : Fin (w.n (m + 1)) => gaussianReal 0 s.toNNReal) = G s) :
    ∫ z, Φ z ∂(netLaw Cb CW σ x w (m + 1)) = ∫ s, G s ∂(netLaw Cb CW σ x w m) := by
  have hT := trans_S (L := L) hCb hCW hσ (x ∘ Fin.cast w.h0) m (by omega) hΦ
  unfold netLaw
  rw [integral_map (PT_Sv Cb CW hσ _ (m + 1)).1.aemeasurable hΦ.1.aestronglyMeasurable,
    integral_map (PT_Sv Cb CW hσ _ m).1.aemeasurable hG.aestronglyMeasurable, hT.2]
  exact integral_congr_ae (ae_of_all _ fun θ => h _)

/-- M8b: the network laws satisfy the chain hypotheses. -/
theorem net_chain (hCb : 0 ≤ Cb) (hCW : 0 ≤ CW) (hσ : PB σ) (x : Fin n0 → ℝ)
    (hK : ∀ ℓ ∈ Finset.Icc 1 (L + 1), 0 < nngpKernel Cb CW σ ℓ x x) :
    Chain (fun w : Net n0 L => w.N) (fun w => w.n) (fun w ℓ => netLaw Cb CW σ x w ℓ)
      (fun ℓ => nngpKernel Cb CW σ ℓ x x) L Cb CW σ := by
  have hnn : ∀ (w : Net n0 L) ℓ, ℓ + 1 ≤ L → 1 ≤ w.n (ℓ + 1) :=
    fun w ℓ hℓ => w.hN.trans (w.hn _ (by omega) hℓ)
  have hwf : ∀ K' : ℝ, PB (fun s => Cb + CW * gS σ s - K') :=
    fun K' => ((PB.const Cb).add ((PB_gS hσ).const_mul CW)).sub (PB.const K')
  refine ⟨fun w => w.hN, fun w ℓ h1 h2 => w.hn ℓ h1 h2,
    fun w ℓ => Measure.isProbabilityMeasure_map (PT_Sv Cb CW hσ _ ℓ).1.aemeasurable,
    fun w ℓ _ F hF => netLaw_int hσ x w ℓ hF, ?_, ?_, ?_, hσ, ?_, ?_, ?_, ?_⟩
  · intro w F
    show ∫ z, F z ∂(netLaw Cb CW σ x w 0) = F (nngpKernel Cb CW σ 1 x x)
    have e1 : ∑ j : Fin (w.n 0), (x ∘ Fin.cast w.h0) j ^ 2 = ∑ j : Fin n0, x j * x j := by
      rw [← Equiv.sum_comp (finCongr w.h0) (fun j => x j * x j)]
      exact Finset.sum_congr rfl fun j _ => by simp [finCongr_apply, sq]
    have e2 : ((w.n 0 : ℕ) : ℝ) = n0 := by rw [w.h0]
    have e : (fun θ : Params w.n L => Sv Cb CW σ θ (x ∘ Fin.cast w.h0) 0) =
        fun _ => nngpKernel Cb CW σ 1 x x := by
      funext θ
      rw [Sv_zero, e1, e2]
      simp only [nngpKernel]
      ring
    unfold netLaw
    rw [e, Measure.map_const, measure_univ, one_smul, integral_dirac]
  · intro ℓ hℓ
    show nngpKernel Cb CW σ (ℓ + 2) x x = Cb + CW * gS σ (nngpKernel Cb CW σ (ℓ + 1) x x)
    rw [← gaussPairAvg_diag hσ.1 (hK (ℓ + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩))]
    rfl
  · intro ℓ h1 h2
    exact hK ℓ (Finset.mem_Icc.2 ⟨h1, by omega⟩)
  · intro w ℓ hℓ
    exact netLaw_trans_eq hCb hCW hσ x w hℓ (Φ := fun z => z - nngpKernel Cb CW σ (ℓ + 2) x x)
      (G := fun s => Cb + CW * gS σ s - nngpKernel Cb CW σ (ℓ + 2) x x)
      (PB.id'.sub (PB.const _)) (hwf (nngpKernel Cb CW σ (ℓ + 2) x x)).1 fun s => trans_mom1 hσ Cb CW _ s (hnn w ℓ hℓ)
  · intro w ℓ hℓ
    exact netLaw_trans_eq hCb hCW hσ x w hℓ
      (Φ := fun z => (z - nngpKernel Cb CW σ (ℓ + 2) x x) ^ 2)
      (G := fun s => (Cb + CW * gS σ s - nngpKernel Cb CW σ (ℓ + 2) x x) ^ 2 +
        CW ^ 2 / w.n (ℓ + 1) * gaussVarSq σ s)
      ((PB.id'.sub (PB.const _)).pow 2) (((hwf (nngpKernel Cb CW σ (ℓ + 2) x x)).pow 2).add ((PB_v hσ).const_mul _)).1
      fun s => trans_mom2 hσ Cb CW _ s (hnn w ℓ hℓ)
  · intro w ℓ hℓ
    exact netLaw_trans_eq hCb hCW hσ x w hℓ
      (Φ := fun z => (z - nngpKernel Cb CW σ (ℓ + 2) x x) ^ 3)
      (G := fun s => (Cb + CW * gS σ s - nngpKernel Cb CW σ (ℓ + 2) x x) ^ 3 +
        3 * CW ^ 2 / w.n (ℓ + 1) * (Cb + CW * gS σ s - nngpKernel Cb CW σ (ℓ + 2) x x) *
          gaussVarSq σ s + CW ^ 3 / (w.n (ℓ + 1) : ℝ) ^ 2 * c3S σ s)
      ((PB.id'.sub (PB.const _)).pow 3)
      ((((hwf (nngpKernel Cb CW σ (ℓ + 2) x x)).pow 3).add (((hwf (nngpKernel Cb CW σ (ℓ + 2) x x)).const_mul _).mul (PB_v hσ))).add
        ((PB_c3 hσ).const_mul _)).1
      fun s => trans_mom3 hσ Cb CW _ s (hnn w ℓ hℓ)
  · intro w ℓ r hℓ
    exact netLaw_trans hCb hCW hσ x w hℓ
      (Φ := fun z => (z - nngpKernel Cb CW σ (ℓ + 2) x x) ^ (2 * r))
      (G := fun s => 2 ^ (2 * r) * ((Cb + CW * gS σ s - nngpKernel Cb CW σ (ℓ + 2) x x) ^ (2 * r) +
        CW ^ (2 * r) * mzB (βS σ s) r / (w.n (ℓ + 1) : ℝ) ^ r))
      ((PB.id'.sub (PB.const _)).pow (2 * r))
      (((((hwf (nngpKernel Cb CW σ (ℓ + 2) x x)).pow (2 * r)).add ((PB_mzB hσ r).const_mul
        (CW ^ (2 * r) / (w.n (ℓ + 1) : ℝ) ^ r))).const_mul (2 ^ (2 * r))).congr fun t => by ring)
      fun s => trans_even hσ Cb CW _ s (hnn w ℓ hℓ) r

lemma kappa_net (hCb : 0 ≤ Cb) (hCW : 0 ≤ CW) (hσ : PB σ) (x : Fin n0 → ℝ) (w : Net n0 L)
    {m : ℕ} (hm : m ≤ L) (i : Fin (w.n (m + 1))) :
    kappa4 Cb CW σ w.n L (x ∘ Fin.cast w.h0) (m + 1) i = var2 (netLaw Cb CW σ x w m) := by
  rw [kappa4_succ hCb hCW hσ _ m (by omega) i]
  unfold var2 netLaw
  rw [integral_map (PT_Sv Cb CW hσ _ m).1.aemeasurable (PB.id'.pow 2).1.aestronglyMeasurable,
    integral_map (PT_Sv Cb CW hσ _ m).1.aemeasurable PB.id'.1.aestronglyMeasurable]

lemma bd_unif {W : Type*} {N : W → ℕ} {F : ℕ → W → ℝ} {k : ℕ} :
    ∀ M : ℕ, (∀ ℓ ≤ M, Bd N (F ℓ) k) → ∃ C : ℝ, ∀ ℓ ≤ M, ∀ w, |F ℓ w| ≤ C / (N w : ℝ) ^ k
  | 0, h => by
    obtain ⟨C, hC⟩ := h 0 le_rfl
    refine ⟨C, fun ℓ hℓ w => ?_⟩
    obtain rfl : ℓ = 0 := by omega
    exact hC w
  | M + 1, h => by
    obtain ⟨C, hC⟩ := bd_unif M fun ℓ hℓ => h ℓ (by omega)
    obtain ⟨C', hC'⟩ := h (M + 1) le_rfl
    refine ⟨max C C', fun ℓ hℓ w => ?_⟩
    have hp : (0 : ℝ) ≤ (N w : ℝ) ^ k := by positivity
    rcases Nat.lt_or_ge ℓ (M + 1) with h1 | h1
    · exact (hC ℓ (by omega) w).trans (div_le_div_of_nonneg_right (le_max_left _ _) hp)
    · obtain rfl : ℓ = M + 1 := by omega
      exact (hC' w).trans (div_le_div_of_nonneg_right (le_max_right _ _) hp)

/-- M9: Theorem 4.2 (first part), with the unused hypotheses dropped. -/
theorem four_point_main (Cb CW : ℝ) (hCb : 0 ≤ Cb) (hCW : 0 < CW)
    (σ : ℝ → ℝ) (hσ : Measurable σ) (hσ_poly : PolyBounded σ)
    (L : ℕ) (hL : 1 ≤ L) (n0 : ℕ) (x : Fin n0 → ℝ)
    (hK : ∀ ℓ ∈ Finset.Icc 1 (L + 1), 0 < nngpKernel Cb CW σ ℓ x x) :
    ∃ C : ℝ, ∀ (N : ℕ) (n : ℕ → ℕ) (h0 : n 0 = n0), 1 ≤ N →
      (∀ ℓ ∈ Finset.Icc 1 L, N ≤ n ℓ) →
      (∀ ℓ ∈ Finset.Icc 1 (L + 1), ∀ i : Fin (n ℓ),
        |kappa4 Cb CW σ n L (x ∘ Fin.cast h0) ℓ i| ≤ C / N) ∧
      (∀ ℓ ∈ Finset.Icc 1 L, ∀ (i : Fin (n (ℓ + 1))) (i' : Fin (n ℓ)),
        |kappa4 Cb CW σ n L (x ∘ Fin.cast h0) (ℓ + 1) i
          - CW ^ 2 / (n ℓ : ℝ) * gaussVarSq σ (nngpKernel Cb CW σ ℓ x x)
          - chiParallel CW σ (nngpKernel Cb CW σ ℓ x x) ^ 2 *
              kappa4 Cb CW σ n L (x ∘ Fin.cast h0) ℓ i'| ≤ C / (N : ℝ) ^ 2) := by
  have hσ' : PB σ := PB.of_polyBounded hσ hσ_poly
  have hc := net_chain hCb hCW.le hσ' x hK
  obtain ⟨C1, h1⟩ := bd_unif (F := fun ℓ (w : Net n0 L) => var2 (netLaw Cb CW σ x w ℓ)) L
    fun ℓ hℓ => hc.P1 hℓ
  obtain ⟨C2, h2⟩ := bd_unif (F := fun ℓ (w : Net n0 L) => var2 (netLaw Cb CW σ x w (ℓ + 1)) -
      CW ^ 2 / w.n (ℓ + 1) * gaussVarSq σ (nngpKernel Cb CW σ (ℓ + 1) x x) -
      (CW * deriv (gS σ) (nngpKernel Cb CW σ (ℓ + 1) x x)) ^ 2 * var2 (netLaw Cb CW σ x w ℓ))
    (L - 1) fun ℓ hℓ => hc.P2 (by omega)
  refine ⟨max C1 C2, fun N n h0 hN hwid => ?_⟩
  let w : Net n0 L := ⟨N, n, h0, hN, fun ℓ a b => hwid ℓ (Finset.mem_Icc.2 ⟨a, b⟩)⟩
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 hN
  constructor
  · intro ℓ hℓ i
    obtain ⟨hl1, hl2⟩ := Finset.mem_Icc.1 hℓ
    obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
    have e : kappa4 Cb CW σ n L (x ∘ Fin.cast h0) (m + 1) i = var2 (netLaw Cb CW σ x w m) :=
      kappa_net hCb hCW.le hσ' x w (m := m) (by omega) i
    rw [e]
    have := h1 m (by omega) w
    rw [pow_one] at this
    exact this.trans (div_le_div_of_nonneg_right (le_max_left _ _) hN'.le)
  · intro ℓ hℓ i i'
    obtain ⟨hl1, hl2⟩ := Finset.mem_Icc.1 hℓ
    obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
    have e1 : kappa4 Cb CW σ n L (x ∘ Fin.cast h0) (m + 1 + 1) i =
        var2 (netLaw Cb CW σ x w (m + 1)) := kappa_net hCb hCW.le hσ' x w (m := m + 1) (by omega) i
    have e2 : kappa4 Cb CW σ n L (x ∘ Fin.cast h0) (m + 1) i' = var2 (netLaw Cb CW σ x w m) :=
      kappa_net hCb hCW.le hσ' x w (m := m) (by omega) i'
    rw [e1, e2]
    exact (h2 m (by omega) w).trans (div_le_div_of_nonneg_right (le_max_right _ _) (by positivity))

end inst

end FW
end LesHouchesWidth

set_option maxHeartbeats 4000000 in
open MeasureTheory ProbabilityTheory LesHouchesWidth in
theorem solution (Cb CW : ℝ) (hCb : 0 ≤ Cb) (hCW : 0 < CW)
    (σ : ℝ → ℝ) (hσ : Measurable σ) (hσ_poly : PolyBounded σ)
    (L : ℕ) (hL : 1 ≤ L) (n0 nOut : ℕ) (hn0 : 1 ≤ n0) (hnOut : 1 ≤ nOut) (x : Fin n0 → ℝ)
    (hK : ∀ ℓ ∈ Finset.Icc 1 (L + 1), 0 < nngpKernel Cb CW σ ℓ x x)
    (A : ℝ) (hA : 1 ≤ A) :
    ∃ C : ℝ, ∀ (N : ℕ) (n : ℕ → ℕ) (h0 : n 0 = n0), 1 ≤ N → n (L + 1) = nOut →
      (∀ ℓ ∈ Finset.Icc 1 L, N ≤ n ℓ ∧ (n ℓ : ℝ) ≤ A * N) →
      (∀ ℓ ∈ Finset.Icc 1 (L + 1), ∀ i : Fin (n ℓ),
        |kappa4 Cb CW σ n L (x ∘ Fin.cast h0) ℓ i| ≤ C / N) ∧
      (∀ ℓ ∈ Finset.Icc 1 L, ∀ (i : Fin (n (ℓ + 1))) (i' : Fin (n ℓ)),
        |kappa4 Cb CW σ n L (x ∘ Fin.cast h0) (ℓ + 1) i
          - CW ^ 2 / (n ℓ : ℝ) * gaussVarSq σ (nngpKernel Cb CW σ ℓ x x)
          - chiParallel CW σ (nngpKernel Cb CW σ ℓ x x) ^ 2 *
              kappa4 Cb CW σ n L (x ∘ Fin.cast h0) ℓ i'| ≤ C / (N : ℝ) ^ 2) := by
  -- `hn0`, `hnOut`, `A`, `hA` and the width upper bound are not needed
  have _unused : 1 ≤ n0 ∧ 1 ≤ nOut ∧ 1 ≤ A := ⟨hn0, hnOut, hA⟩
  obtain ⟨C, hC⟩ := LesHouchesWidth.FW.four_point_main Cb CW hCb hCW σ hσ hσ_poly L hL n0 x hK
  exact ⟨C, fun N n h0 hN _ hw => hC N n h0 hN fun ℓ hℓ => (hw ℓ hℓ).1⟩
