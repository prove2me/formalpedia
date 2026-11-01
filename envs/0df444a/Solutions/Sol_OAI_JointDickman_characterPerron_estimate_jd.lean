-- Prove2me | solution 1 for OAI.JointDickman.characterPerron_estimate_jd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:30:59.627094+00:00
-- url     : https://prove2.me/submissions/432670e2-c92d-4559-a941-93c340d37c19

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_OAIQ083J003

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_AnalyticLogBranch
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Analytic logarithms on the zero-free contour domains -/
namespace JointDickman
open Filter Set
open scoped Topology

theorem analyticAt_of_continuousAt_exp {f : ℂ → ℂ} {x : ℂ}
    (hf : ContinuousAt f x) (he : AnalyticAt ℂ (fun y => Complex.exp (f y)) x) :
    AnalyticAt ℂ f x := by
  have hE : AnalyticAt ℂ Complex.exp (f x) := analyticAt_cexp
  have hd : deriv Complex.exp (f x) ≠ 0 := by
    rw [Complex.deriv_exp]
    exact Complex.exp_ne_zero _
  let r := hE.hasStrictDerivAt.localInverse _ _ _ hd
  have hr : AnalyticAt ℂ r (Complex.exp (f x)) := hE.analyticAt_localInverse hd
  have hi : (fun y => r (Complex.exp (f y))) =ᶠ[𝓝 x] f :=
    hf.eventually (hE.hasStrictDerivAt.eventually_left_inverse hd)
  have har : AnalyticAt ℂ (fun y => r (Complex.exp (f y))) x :=
    AnalyticAt.comp (f := fun y => Complex.exp (f y)) hr he
  exact har.congr hi

theorem exists_analytic_log_on {U : Set ℂ} (hUc : IsSimplyConnected U) (hUo : IsOpen U)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U) (hne : ∀ x ∈ U, g x ≠ 0) :
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f U ∧ ∀ x ∈ U, Complex.exp (f x) = g x := by
  obtain ⟨f,hf,he⟩ := Complex.exists_continuousOn_eqOn_exp_comp hUc hUo hg.continuousOn
    (by rintro ⟨x,hx,heq⟩; exact hne x hx heq)
  refine ⟨f,fun x hx => ?_,he⟩
  apply analyticAt_of_continuousAt_exp (hf.continuousAt (hUo.mem_nhds hx))
  apply (hg x hx).congr
  exact (Filter.eventuallyEq_of_mem (hUo.mem_nhds hx) (fun y hy => he hy)).symm

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_AnalyticLogUniqueness
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniqueness of normalized analytic logarithms -/
namespace JointDickman
open Set Filter
open scoped Topology

theorem analytic_log_unique {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U)
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (he : ∀ s ∈ U, Complex.exp (f s) = Complex.exp (g s))
    {x₀ : ℂ} (hx₀ : x₀ ∈ U) (h₀ : f x₀ = g x₀) : EqOn f g U := by
  have hd : ∀ s ∈ U, deriv f s = deriv g s := by
    intro s hs
    have heq : (fun t => Complex.exp (f t)) =ᶠ[𝓝 s] (fun t => Complex.exp (g t)) := by
      filter_upwards [hU.mem_nhds hs] with t ht
      exact he t ht
    have hh := ((hf s hs).differentiableAt.hasDerivAt.cexp.congr_of_eventuallyEq heq.symm).unique
      (hg s hs).differentiableAt.hasDerivAt.cexp
    rw [he s hs] at hh
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) hh
  exact hU.eqOn_of_deriv_eq hc hf.differentiableOn hg.differentiableOn hd hx₀ h₀

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.PrimeGaps_DirichletGrowth
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

open scoped ComplexConjugate

open Filter Topology

open Complex Filter Topology

open Complex Filter Topology Set MeasureTheory Asymptotics

lemma discrepancyTail_integrable {A : ℝ → ℂ} {u D : ℝ} (hu : 0 < u) (hD : 0 ≤ D)
    (hA : Measurable A) (hbound : ∀ t, u < t → ‖A t‖ ≤ D) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t => A t * (t:ℂ)^(-(s+1))) (Ioi u) := by
  have hp : (-(s+1)).re < -1 := by simp only [neg_re,add_re,one_re] <;> linarith
  have hi := (integrableOn_Ioi_norm_cpow_of_lt hp hu).const_mul D
  have hm := (integrableOn_Ioi_cpow_of_lt hp hu).aestronglyMeasurable
  refine hi.mono (hA.aestronglyMeasurable.restrict.mul hm) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hD (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_right (hbound t ht) (norm_nonneg _)

lemma discrepancyTail_norm_le {A : ℝ → ℂ} {u D : ℝ} (hu : 0 < u) (_hD : 0 ≤ D)
    (_hA : Measurable A) (hbound : ∀ t, u < t → ‖A t‖ ≤ D) {s : ℂ} (hs : 0 < s.re) :
    ‖discrepancyTail A u s‖ ≤ D * u^(-s.re)/s.re := by
  have hi := (integrableOn_Ioi_rpow_of_lt (by linarith : -s.re-1 < -1) hu).const_mul D
  calc
    _ ≤ ∫ t in Ioi u, D*t^(-s.re-1) := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (hu.trans ht)]
      simp only [neg_re,add_re,one_re,neg_add_rev]
      have he : -1 + -s.re = -s.re-1 := by ring
      rw [he]
      exact mul_le_mul_of_nonneg_right (hbound t ht) (Real.rpow_nonneg (hu.trans ht).le _)
    _ = _ := by
      rw [integral_const_mul,integral_Ioi_rpow_of_lt (by linarith : -s.re-1 < -1) hu]
      ring_nf

lemma discrepancyTail_eq_mellin {A : ℝ → ℂ} {u : ℝ} (hu : 0 ≤ u) (s : ℂ) :
    discrepancyTail A u s = mellin ((Ioi u).indicator A) (-s) := by
  rw [mellin]
  simp_rw [←Set.indicator_smul]
  rw [integral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi]
  have he : Ioi u ∩ Ioi 0 = Ioi u := Set.inter_eq_left.mpr (fun t ht => hu.trans_lt ht)
  rw [he]
  unfold discrepancyTail
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 2
  ring

lemma discrepancyTail_differentiableAt {A : ℝ → ℂ} {u D : ℝ} (hu : 0 < u) (hD : 0 ≤ D)
    (hA : Measurable A) (hbound : ∀ t, u < t → ‖A t‖ ≤ D) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (discrepancyTail A u) s := by
  let B := (Ioi u).indicator A
  have hm : Measurable B := hA.indicator measurableSet_Ioi
  have hb : ∀ t, ‖B t‖ ≤ D := by
    intro t
    by_cases ht : u < t
    · simpa [B,ht] using hbound t ht
    · simpa [B,ht] using hD
  have hloc : LocallyIntegrableOn B (Ioi 0) :=
    ((locallyIntegrable_const D).mono hm.aestronglyMeasurable
      (.of_forall (fun t => (hb t).trans (le_abs_self D)))).locallyIntegrableOn _
  have htop : B =O[atTop] (fun t : ℝ => t^(-(0:ℝ))) := by
    refine isBigO_iff.mpr ⟨D,Eventually.of_forall ?_⟩
    intro t
    simpa using hb t
  have hbot : B =O[𝓝[>] 0] (fun t : ℝ => t^(-(-s.re-1))) := by
    refine isBigO_iff.mpr ⟨0,?_⟩
    filter_upwards [nhdsWithin_le_nhds (gt_mem_nhds hu)] with t ht
    simp [B,not_lt.mpr ht.le]
  have hd := mellin_differentiableAt_of_isBigO_rpow hloc htop
    (by simpa using hs : (-s).re < 0) hbot (by simp : -s.re-1 < (-s).re)
  have he : discrepancyTail A u = fun z => mellin B (-z) := funext (discrepancyTail_eq_mellin hu.le)
  rw [he]
  exact hd.comp s differentiableAt_id.neg

open Finset

lemma periodic_sum_norm_le {f : ℕ → ℂ} {q : ℕ} (hq : 0 < q)
    (hp : ∀ n, f (q+n) = f n) (hz : ∑ n ∈ range q, f n = 0)
    (hb : ∀ n, ‖f n‖ ≤ 1) (N : ℕ) : ‖∑ n ∈ range N, f n‖ ≤ q := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases hN : N < q
    · calc
        _ ≤ ∑ n ∈ range N, ‖f n‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ range N, (1:ℝ) := sum_le_sum (fun n _ => hb n)
        _ = N := by simp
        _ ≤ q := by exact_mod_cast hN.le
    · have he : q+(N-q) = N := Nat.add_sub_of_le (not_lt.mp hN)
      rw [←he, sum_range_add, hz, zero_add]
      simp_rw [hp]
      exact ih _ (Nat.sub_lt (lt_of_lt_of_le hq (not_lt.mp hN)) hq)

lemma char_sum_range_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : ∑ n ∈ range q, χ (n : ZMod q) = 0 := by
  rw [←Fin.sum_univ_eq_sum_range]
  have he := (ZMod.finEquiv q).toEquiv.sum_comp χ
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q =>
    have hz := he.trans (MulChar.sum_eq_zero_of_ne_one hχ)
    change (∑ i : Fin (q+1), χ i) = 0 at hz
    calc
      _ = ∑ i : Fin (q+1), χ (i : Fin (q+1)) := by
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
        exact Fin.cast_val_eq_self i
      _ = 0 := hz

lemma char_sum_Icc_norm_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (N : ℕ) : ‖∑ n ∈ Icc 1 N, χ (n : ZMod q)‖ ≤ q+1 := by
  have hr := periodic_sum_norm_le (NeZero.pos q)
    (f := fun n => χ (n : ZMod q)) (by intro n; simp)
    (char_sum_range_zero hχ) (fun n => χ.norm_le_one _) (N+1)
  have he : ∑ n ∈ range (N+1), χ (n : ZMod q) =
      χ (0 : ZMod q) + ∑ n ∈ Icc 1 N, χ (n : ZMod q) := by
    rw [Nat.range_succ_eq_Icc_zero, ←Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le N)]
    simp
  rw [he] at hr
  calc
    _ = ‖(χ (0 : ZMod q) + ∑ n ∈ Icc 1 N, χ (n : ZMod q)) - χ 0‖ := by congr 1; ring
    _ ≤ ‖χ (0 : ZMod q) + ∑ n ∈ Icc 1 N, χ (n : ZMod q)‖ + ‖χ 0‖ := norm_sub_le _ _
    _ ≤ q+1 := add_le_add hr (χ.norm_le_one _)

lemma measurable_seriesDiscrepancy (f : ℕ → ℂ) (c : ℂ) :
    Measurable (seriesDiscrepancy f c) := by
  exact ((measurable_of_countable (fun N : ℕ => ∑ n ∈ Icc 1 N, f n)).comp
    Nat.measurable_floor).sub (measurable_const.mul Complex.continuous_ofReal.measurable)

lemma regularSeries_differentiableAt {f : ℕ → ℂ} {c : ℂ} {D : ℝ} (hD : 0 ≤ D)
    (hb : ∀ t, 1 < t → ‖seriesDiscrepancy f c t‖ ≤ D) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (regularSeries f c) s := by
  exact (differentiableAt_const c).add (differentiableAt_id.mul
    (discrepancyTail_differentiableAt zero_lt_one hD (measurable_seriesDiscrepancy f c) hb hs))

lemma regularSeries_eq_LSeries_sub {f : ℕ → ℂ} {c : ℂ} {D : ℝ}
    (hf : ∀ n, ‖f n‖ ≤ 1) (hD : 0 ≤ D)
    (hb : ∀ t, 1 < t → ‖seriesDiscrepancy f c t‖ ≤ D) {s : ℂ} (hs : 1 < s.re) :
    regularSeries f c s = LSeries f s - c/(s-1) := by
  have hO : (fun n => ∑ k ∈ Icc 1 n, ‖f k‖) =O[atTop] (fun n => (n:ℝ)^(1:ℝ)) := by
    refine isBigO_iff.mpr ⟨1, .of_forall (fun n => ?_)⟩
    simp only [Real.rpow_one, one_mul, Real.norm_eq_abs]
    rw [abs_of_nonneg (sum_nonneg (fun _ _ => norm_nonneg _))]
    calc
      _ ≤ ∑ _k ∈ Icc 1 n, (1:ℝ) := sum_le_sum (fun n _ => hf n)
      _ ≤ |(n:ℝ)| := by simp
  rw [LSeries_eq_mul_integral' f zero_le_one hs hO]
  have hiA := discrepancyTail_integrable zero_lt_one hD (measurable_seriesDiscrepancy f c) hb
    (zero_lt_one.trans hs)
  have hi := integrableOn_Ioi_cpow_of_lt (by simpa using neg_lt_neg hs : (-s).re < -1) zero_lt_one
  have he (t : ℝ) (ht : 1 < t) :
      (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t:ℂ)^(-(s+1)) =
      seriesDiscrepancy f c t * (t:ℂ)^(-(s+1)) + c*(t:ℂ)^(-s) := by
    have ht0 : (t:ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans ht).ne'
    have ht1 : (t:ℂ)*(t:ℂ)^(-(s+1)) = (t:ℂ)^(-s) := by
      nth_rw 1 [←Complex.cpow_one (t:ℂ)]
      rw [←Complex.cpow_add _ _ ht0]
      congr 1
      ring
    dsimp [seriesDiscrepancy]
    rw [sub_mul, mul_assoc c, ht1]
    ring
  have hs0 : s-1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this <;> linarith
  have hv : ∫ t in Ioi (1:ℝ), (t:ℂ)^(-s) = 1/(s-1) := by
    rw [integral_Ioi_cpow_of_lt (by simpa using neg_lt_neg hs : (-s).re < -1) zero_lt_one]
    simp only [ofReal_one, one_cpow]
    have he : -s+1 = -(s-1) := by ring
    rw [he, neg_div_neg_eq]
  rw [setIntegral_congr_fun measurableSet_Ioi he,
    integral_add hiA (hi.const_mul c), integral_const_mul, hv]
  dsimp [regularSeries,discrepancyTail]
  field_simp [hs0]
  ring

lemma sum_Icc_zero_eq {f : ℕ → ℂ} (hf : f 0 = 0) (N : ℕ) :
    ∑ k ∈ Icc 0 N, f k = ∑ k ∈ Icc 1 N, f k := by
  rw [←Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le N)]
  simp [hf]

lemma weighted_sum_abel {f : ℕ → ℂ} (hf : f 0 = 0) {N : ℕ} (hN : 1 ≤ N)
    {s : ℂ} (hs : 0 < s.re) :
    ∑ n ∈ Icc 1 N, f n * (n:ℂ)^(-s) =
      (∑ n ∈ Icc 1 N, f n)*(N:ℂ)^(-s) +
        s*∫ t in (1:ℝ)..N, (∑ n ∈ Icc 1 ⌊t⌋₊, f n)*(t:ℂ)^(-(s+1)) := by
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hs0 : s ≠ 0 := Complex.ne_zero_of_re_pos hs
  have hd (t:ℝ) (ht : t ∈ Set.Icc 1 (N:ℝ)) :
      HasDerivAt (fun t : ℝ => (t:ℂ)^(-s)) ((-s)*(t:ℂ)^(-(s+1))) t := by
    rw [show -(s+1) = -s-1 by ring]
    exact hasDerivAt_ofReal_cpow_const ((zero_lt_one.trans_le ht.1).ne') (neg_ne_zero.mpr hs0)
  have hcont : ContinuousOn (fun t : ℝ => (-s)*(t:ℂ)^(-(s+1))) (Set.Icc 1 (N:ℝ)) := by
    intro t ht
    exact (continuousAt_const.mul (Complex.continuousAt_ofReal_cpow_const _ _
      (.inr (zero_lt_one.trans_le ht.1).ne'))).continuousWithinAt
  have hi : IntegrableOn (deriv (fun t:ℝ => (t:ℂ)^(-s))) (Set.Icc 1 (N:ℝ)) :=
    hcont.integrableOn_Icc.congr_fun (fun t ht => (hd t ht).deriv.symm) measurableSet_Icc
  have ha := sum_mul_eq_sub_sub_integral_mul' f hN (fun t ht => (hd t (by simpa using ht)).differentiableAt) (by simpa using hi)
  have he : (insert 1 (Finset.Ioc 1 N) : Finset ℕ) = Finset.Icc 1 N := by
    ext k
    simp only [Finset.mem_insert,Finset.mem_Ioc,Finset.mem_Icc]
    omega
  have hint : (∫ t in Set.Ioc (1:ℝ) (N:ℝ),
      deriv (fun t:ℝ => (t:ℂ)^(-s)) t * ∑ k ∈ Icc 0 ⌊t⌋₊, f k) =
      (-s)*∫ t in (1:ℝ)..N, (∑ k ∈ Icc 1 ⌊t⌋₊, f k)*(t:ℂ)^(-(s+1)) := by
    rw [intervalIntegral.integral_of_le hNR, ←integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [(hd t ⟨ht.1.le,ht.2⟩).deriv,sum_Icc_zero_eq hf]
    ring
  simp only [Nat.cast_one, Complex.ofReal_natCast, Complex.ofReal_one] at ha
  rw [hint] at ha
  simp only [one_cpow,one_mul,sum_Icc_zero_eq hf,Finset.Icc_self,sum_singleton] at ha
  conv_lhs => rw [←he,sum_insert (by simp)]
  simp only [Nat.cast_one,one_cpow,mul_one]
  simp_rw [mul_comm (f _) ((_:ℂ)^(-s))]
  rw [ha]
  ring

lemma cpow_sub_eq_mul_intervalIntegral {N : ℝ} (hN : 1 ≤ N) (s : ℂ) :
    (N:ℂ)^(1-s)-1 = (1-s)*∫ t in (1:ℝ)..N, (t:ℂ)^(-s) := by
  by_cases hs : s = 1
  · subst s
    simp
  · have hn : (0:ℝ) ∉ Set.uIcc 1 N := by rw [Set.uIcc_of_le hN]; simp
    rw [integral_cpow (.inr ⟨by simpa using hs,hn⟩)]
    simp only [Complex.ofReal_one,one_cpow]
    have he : -s+1 = 1-s := by ring
    rw [he]
    field_simp

lemma regularSeries_cutoff {f : ℕ → ℂ} {c : ℂ} {D : ℝ} (hf : f 0 = 0)
    (hD : 0 ≤ D) (hb : ∀ t, 1 < t → ‖seriesDiscrepancy f c t‖ ≤ D)
    {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    regularSeries f c s = (∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)) -
      seriesDiscrepancy f c N * (N:ℂ)^(-s) +
      s*discrepancyTail (seriesDiscrepancy f c) N s -
      c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s) := by
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (N:ℂ) ≠ 0 := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN).ne'
  have hi := discrepancyTail_integrable zero_lt_one hD (measurable_seriesDiscrepancy f c) hb hs
  have htail := intervalIntegral.integral_Ioi_sub_Ioi hi hNR
  have hp : ∀ t ∈ Set.Icc (1:ℝ) (N:ℝ),
      (t:ℂ)*(t:ℂ)^(-(s+1)) = (t:ℂ)^(-s) := by
    intro t ht
    have ht0 : (t:ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le ht.1).ne'
    nth_rw 1 [←Complex.cpow_one (t:ℂ)]
    rw [←Complex.cpow_add _ _ ht0]
    congr 1
    ring
  have hip : IntervalIntegrable (fun t:ℝ => (t:ℂ)^(-s)) volume 1 N :=
    intervalIntegral.intervalIntegrable_cpow (.inr (by rw [Set.uIcc_of_le hNR]; simp))
  have hiA : IntervalIntegrable (fun t:ℝ => seriesDiscrepancy f c t*(t:ℂ)^(-(s+1))) volume 1 N :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hNR).mpr (hi.mono_set Set.Ioc_subset_Ioi_self)
  have hint : (∫ t in (1:ℝ)..N, (∑ n ∈ Icc 1 ⌊t⌋₊, f n)*(t:ℂ)^(-(s+1))) =
      (∫ t in (1:ℝ)..N, seriesDiscrepancy f c t*(t:ℂ)^(-(s+1))) +
        c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s) := by
    rw [←intervalIntegral.integral_const_mul, ←intervalIntegral.integral_add hiA (hip.const_mul c)]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hNR] at ht
    dsimp [seriesDiscrepancy]
    rw [sub_mul,mul_assoc c,hp t ht]
    ring
  have hab := weighted_sum_abel hf hN hs
  rw [hint, ←htail] at hab
  have hpow : (N:ℂ)*(N:ℂ)^(-s) = (N:ℂ)^(1-s) := by
    nth_rw 1 [←Complex.cpow_one (N:ℂ)]
    rw [←Complex.cpow_add _ _ hn0]
    congr 1
  have hc := cpow_sub_eq_mul_intervalIntegral hNR s
  simp only [Complex.ofReal_natCast] at hc
  dsimp [regularSeries,discrepancyTail]
  rw [hab]
  simp only [seriesDiscrepancy,Nat.floor_natCast,Complex.ofReal_natCast]
  rw [sub_mul,mul_assoc c,hpow,sub_eq_iff_eq_add.mp hc]
  ring

lemma sum_cpow_norm_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {ε : ℝ} (hε : 0 < ε)
    {s : ℂ} (hs : 1-ε ≤ s.re) {N : ℕ} (_hN : 1 ≤ N) :
    ‖∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)‖ ≤
      (∑' n : ℕ, (n:ℝ)^(-1-ε)) * (N:ℝ)^(2*ε) := by
  have hsumm : Summable (fun n : ℕ => (n:ℝ)^(-1-ε)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ‖f n*(n:ℂ)^(-s)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Icc 1 N, (n:ℝ)^(-1-ε)*(N:ℝ)^(2*ε) := by
      apply sum_le_sum
      intro n hn
      have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
      have hnN : (n:ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
      have hn0 := zero_lt_one.trans_le hn1
      rw [norm_mul]
      have hn0C : (n:ℂ) = ((n:ℝ):ℂ) := by simp
      rw [hn0C,Complex.norm_cpow_eq_rpow_re_of_pos hn0,Complex.neg_re]
      calc
        _ ≤ (n:ℝ)^(-s.re) := by
          simpa using mul_le_mul_of_nonneg_right (hf n) (Real.rpow_nonneg hn0.le (-s.re))
        _ ≤ (n:ℝ)^(-1+ε) := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
        _ = (n:ℝ)^(-1-ε)*(n:ℝ)^(2*ε) := by rw [←Real.rpow_add hn0]; congr 1; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hn0.le hnN (by positivity))
          (Real.rpow_nonneg hn0.le _)
    _ = (∑ n ∈ Icc 1 N, (n:ℝ)^(-1-ε))*(N:ℝ)^(2*ε) := by rw [sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hsumm.sum_le_tsum _ (fun n _ => Real.rpow_nonneg n.cast_nonneg _))
      (Real.rpow_nonneg N.cast_nonneg _)

lemma norm_intervalIntegral_cpow_le {ε N : ℝ} (hε : 0 < ε) (hN : 1 ≤ N)
    {s : ℂ} (hs : 1-ε ≤ s.re) :
    ‖∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ ≤ N^ε/ε := by
  have hn : (0:ℝ) ∉ Set.uIcc 1 N := by rw [Set.uIcc_of_le hN]; simp
  calc
    _ ≤ ∫ t in (1:ℝ)..N, t^(-1+ε) := by
      apply intervalIntegral.norm_integral_le_of_norm_le hN
        (.of_forall (fun t ht => ?_)) (intervalIntegral.intervalIntegrable_rpow (.inr hn))
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht.1),Complex.neg_re]
      exact Real.rpow_le_rpow_of_exponent_le ht.1.le (by linarith)
    _ = (N^ε-1)/ε := by
      rw [integral_rpow (.inl (by linarith : -1 < -1+ε))]
      have he : -1+ε+1 = ε := by ring
      simp [he]
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hε.le

lemma regularSeries_norm_cutoff {f : ℕ → ℂ} {c : ℂ} {D ε : ℝ}
    (hf0 : f 0 = 0) (hf : ∀ n, ‖f n‖ ≤ 1) (hc : ‖c‖ ≤ 1) (hD : 0 ≤ D)
    (hb : ∀ t, 1 ≤ t → ‖seriesDiscrepancy f c t‖ ≤ D)
    (hε : 0 < ε) (hε1 : ε ≤ 1/2) {N : ℕ} (hN : 1 ≤ N) {s : ℂ}
    (hs : 1-ε ≤ s.re) (hNs : D*(1+‖s‖) ≤ N) :
    ‖regularSeries f c s‖ ≤ ((∑' n : ℕ, (n:ℝ)^(-1-ε))+2+1/ε)*(N:ℝ)^(2*ε) := by
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hNP := zero_lt_one.trans_le hNR
  have hs0 : 0 < s.re := by linarith
  have hhalf : 1/2 ≤ s.re := by linarith
  have htail := discrepancyTail_norm_le hNP hD (measurable_seriesDiscrepancy f c)
    (fun t ht => hb t (hNR.trans ht.le)) hs0
  have hboundary : ‖seriesDiscrepancy f c N * (N:ℂ)^(-s)‖ ≤ D*(N:ℝ)^(-s.re) := by
    rw [norm_mul, ←Complex.ofReal_natCast N, Complex.norm_cpow_eq_rpow_re_of_pos hNP,Complex.neg_re]
    exact mul_le_mul_of_nonneg_right (hb _ hNR) (Real.rpow_nonneg hNP.le _)
  have hsmall : ‖seriesDiscrepancy f c N * (N:ℂ)^(-s)‖ +
      ‖s*discrepancyTail (seriesDiscrepancy f c) N s‖ ≤ 2*(N:ℝ)^ε := by
    have ht : D*(N:ℝ)^(-s.re)/s.re ≤ 2*D*(N:ℝ)^(-s.re) := by
      apply (div_le_iff₀ hs0).mpr
      have hn := Real.rpow_nonneg hNP.le (-s.re)
      nlinarith [mul_nonneg hD hn,mul_nonneg (mul_nonneg hD hn) (sub_nonneg.mpr hhalf)]
    have he : (N:ℝ)*(N:ℝ)^(-s.re) ≤ (N:ℝ)^ε := by
      nth_rw 1 [←Real.rpow_one (N:ℝ)]
      rw [←Real.rpow_add hNP]
      apply Real.rpow_le_rpow_of_exponent_le hNR
      linarith
    calc
      _ ≤ D*(N:ℝ)^(-s.re) + ‖s‖*(2*D*(N:ℝ)^(-s.re)) := by
        nth_rw 2 [norm_mul]
        exact add_le_add hboundary (mul_le_mul_of_nonneg_left (htail.trans ht) (norm_nonneg s))
      _ ≤ 2*(N:ℝ)*(N:ℝ)^(-s.re) := by
        have hcoeff : D+2*‖s‖*D ≤ 2*(N:ℝ) := by nlinarith
        nlinarith [mul_nonneg (sub_nonneg.mpr hcoeff) (Real.rpow_nonneg hNP.le (-s.re))]
      _ ≤ _ := by nlinarith [he]
  have hi : ‖c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ ≤ (N:ℝ)^ε/ε := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans (by
      simpa using norm_intervalIntegral_cpow_le hε hNR hs)
  have hp : (N:ℝ)^ε ≤ (N:ℝ)^(2*ε) := Real.rpow_le_rpow_of_exponent_le hNR (by linarith)
  rw [regularSeries_cutoff hf0 hD (fun t ht => hb t ht.le) hN hs0]
  calc
    _ ≤ ‖∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)‖ +
        (‖seriesDiscrepancy f c N * (N:ℂ)^(-s)‖ +
        ‖s*discrepancyTail (seriesDiscrepancy f c) N s‖) +
        ‖c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ := by
      calc
        _ ≤ ‖(∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)) - seriesDiscrepancy f c N * (N:ℂ)^(-s) +
             s*discrepancyTail (seriesDiscrepancy f c) N s‖ +
             ‖c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ := norm_sub_le _ _
        _ ≤ (‖(∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)) - seriesDiscrepancy f c N * (N:ℂ)^(-s)‖ +
             ‖s*discrepancyTail (seriesDiscrepancy f c) N s‖) +
             ‖c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ := add_le_add (norm_add_le _ _) le_rfl
        _ ≤ _ := by
          have htri := norm_sub_le (∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)) (seriesDiscrepancy f c N * (N:ℂ)^(-s))
          linarith
    _ ≤ ((∑' n : ℕ, (n:ℝ)^(-1-ε)))*(N:ℝ)^(2*ε) +
      2*(N:ℝ)^ε+(N:ℝ)^ε/ε := add_le_add (add_le_add (sum_cpow_norm_le hf hε hs hN) hsmall) hi
    _ ≤ ((∑' n : ℕ, (n:ℝ)^(-1-ε)))*(N:ℝ)^(2*ε) +
      2*(N:ℝ)^(2*ε)+(N:ℝ)^(2*ε)/ε := by
        linarith [div_le_div_of_nonneg_right hp hε.le]
    _ = _ := by ring

lemma regularSeries_norm_small_power {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : ℕ → ℂ) (c : ℂ) (D : ℝ),
      f 0 = 0 → (∀ n, ‖f n‖ ≤ 1) → ‖c‖ ≤ 1 → 0 ≤ D →
      (∀ t, 1 ≤ t → ‖seriesDiscrepancy f c t‖ ≤ D) →
      ∀ s : ℂ, 1-ε ≤ s.re →
      ‖regularSeries f c s‖ ≤ K*((D+1)*(‖s‖+2))^(2*ε) := by
  let K₀ := (∑' n : ℕ, (n:ℝ)^(-1-ε))+2+1/ε
  have hK₀ : 0 < K₀ := by
    have ht : 0 ≤ ∑' n : ℕ, (n:ℝ)^(-1-ε) := tsum_nonneg (fun n => Real.rpow_nonneg n.cast_nonneg _)
    dsimp [K₀]
    positivity
  refine ⟨K₀*2^(2*ε), by positivity, ?_⟩
  intro f c D hf0 hf hc hD hb s hs
  let B := (D+1)*(‖s‖+2)
  have hB : 1 ≤ B := by dsimp [B] <;> nlinarith [norm_nonneg s]
  let N := ⌈B⌉₊
  have hBN : B ≤ (N:ℝ) := Nat.le_ceil B
  have hN : 1 ≤ N := by exact_mod_cast (hB.trans hBN)
  have hN2 : (N:ℝ) ≤ 2*B := by
    have := Nat.ceil_lt_add_one (zero_lt_one.trans_le hB).le
    change (N:ℝ) < B+1 at this
    linarith
  have hcut := regularSeries_norm_cutoff hf0 hf hc hD hb hε hε1 hN hs
    (show D*(1+‖s‖) ≤ (N:ℝ) from (by dsimp [B] at hBN <;> nlinarith [norm_nonneg s]))
  calc
    _ ≤ K₀*(N:ℝ)^(2*ε) := hcut
    _ ≤ K₀*(2*B)^(2*ε) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow N.cast_nonneg hN2 (by positivity)) hK₀.le
    _ = _ := by rw [Real.mul_rpow (by norm_num) (by linarith : 0 ≤ B)]; ring

lemma positiveCoefficients_zero (f : ℕ → ℂ) : positiveCoefficients f 0 = 0 := by simp [positiveCoefficients]

lemma positiveCoefficients_norm_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (n : ℕ) :
    ‖positiveCoefficients f n‖ ≤ 1 := by
  by_cases hn : n=0 <;> simp [positiveCoefficients,hn,hf]

lemma sum_positiveCoefficients (f : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, positiveCoefficients f n = ∑ n ∈ Icc 1 N, f n := by
  apply sum_congr rfl
  intro n hn
  simp [positiveCoefficients,show n ≠ 0 from Nat.ne_of_gt (mem_Icc.mp hn).1]

lemma LSeries_positiveCoefficients (f : ℕ → ℂ) (s : ℂ) :
    LSeries (positiveCoefficients f) s = LSeries f s := by
  apply LSeries_congr
  intro n hn
  simp [positiveCoefficients,hn]

lemma discrepancy_character_bound {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (t : ℝ) :
    ‖seriesDiscrepancy (positiveCoefficients (fun n => χ (n : ZMod q))) 0 t‖ ≤ q+1 := by
  simpa [seriesDiscrepancy,sum_positiveCoefficients] using char_sum_Icc_norm_le hχ ⌊t⌋₊

lemma discrepancy_constant_bound {t : ℝ} (ht : 1 ≤ t) :
    ‖seriesDiscrepancy (positiveCoefficients (fun _ => 1)) 1 t‖ ≤ 1 := by
  simp only [seriesDiscrepancy,sum_positiveCoefficients,Finset.sum_const,nsmul_eq_mul,
    mul_one,Nat.card_Icc,Nat.add_sub_cancel,one_mul]
  rw [←Complex.ofReal_natCast,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  have ht0 := (show (0:ℝ) ≤ t by linarith)
  rw [abs_of_nonpos (sub_nonpos.mpr (Nat.floor_le ht0))]
  have := Nat.lt_floor_add_one t
  linarith

lemma regularSeries_character_eq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    regularSeries (positiveCoefficients (fun n => χ (n : ZMod q))) 0 s = χ.LFunction s := by
  let f := positiveCoefficients (fun n => χ (n : ZMod q))
  have hfrac : AnalyticOnNhd ℂ (regularSeries f 0) {s : ℂ | 0 < s.re} := by
    apply DifferentiableOn.analyticOnNhd ?_ (continuous_re.isOpen_preimage _ isOpen_Ioi)
    intro s hs
    exact (regularSeries_differentiableAt (by positivity : (0:ℝ) ≤ q+1)
      (fun t _ => discrepancy_character_bound hχ t) hs).differentiableWithinAt
  have hL : AnalyticOnNhd ℂ χ.LFunction {s : ℂ | 0 < s.re} :=
    fun s _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt s
  have he : regularSeries f 0 =ᶠ[𝓝 (2:ℂ)] χ.LFunction := by
    filter_upwards [(continuous_re.tendsto (2:ℂ)).eventually (lt_mem_nhds (by norm_num : (1:ℝ) < (2:ℂ).re))] with z hz
    rw [regularSeries_eq_LSeries_sub (positiveCoefficients_norm_le (fun n => χ.norm_le_one _))
      (by positivity : (0:ℝ) ≤ q+1) (fun t _ => discrepancy_character_bound hχ t) hz]
    simp only [zero_div,sub_zero]
    rw [LSeries_positiveCoefficients,DirichletCharacter.LFunction_eq_LSeries χ hz]
  exact hfrac.eqOn_of_preconnected_of_eventuallyEq hL (convex_halfSpace_re_gt 0).isPreconnected
    (show (2:ℂ) ∈ {s:ℂ | 0 < s.re} by norm_num) he hs

lemma LFunction_norm_small_power {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ s : ℂ, 1-ε ≤ s.re →
      ‖χ.LFunction s‖ ≤ K*((q+2)*(‖s‖+2))^(2*ε) := by
  obtain ⟨K,hK,h⟩ := regularSeries_norm_small_power hε hε1
  refine ⟨K,hK,fun q _ χ hχ s hs => ?_⟩
  have he := h _ 0 (q+1) (positiveCoefficients_zero _) (positiveCoefficients_norm_le (fun n => χ.norm_le_one _))
    (by simp) (by positivity) (fun t _ => discrepancy_character_bound hχ t) s hs
  rw [regularSeries_character_eq hχ (by linarith)] at he
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  congr 3
  ring

lemma regularSeries_deriv_norm_small_power {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : ℕ → ℂ) (c : ℂ) (D : ℝ),
      f 0 = 0 → (∀ n, ‖f n‖ ≤ 1) → ‖c‖ ≤ 1 → 0 ≤ D →
      (∀ t, 1 ≤ t → ‖seriesDiscrepancy f c t‖ ≤ D) →
      ∀ s : ℂ, 1-ε/2 ≤ s.re →
      ‖deriv (regularSeries f c) s‖ ≤ K*((D+1)*(‖s‖+2))^(2*ε) := by
  obtain ⟨K,hK,h⟩ := regularSeries_norm_small_power hε hε1
  refine ⟨K*2^(2*ε)/(ε/2),by positivity,?_⟩
  intro f c D hf0 hf hc hD hb s hs
  have hε2 : 0 < ε/2 := by positivity
  have hre (z:ℂ) (hz : dist z s ≤ ε/2) : 1-ε ≤ z.re := by
    have hd := Complex.re_le_norm (s-z)
    rw [Complex.sub_re,←dist_eq_norm,dist_comm] at hd
    linarith
  have hd : DiffContOnCl ℂ (regularSeries f c) (Metric.ball s (ε/2)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hε2.ne']
    intro z hz
    exact (regularSeries_differentiableAt hD (fun t ht => hb t ht.le) (by
      have := hre z (Metric.mem_closedBall.mp hz)
      linarith)).differentiableWithinAt
  have hbnd (z:ℂ) (hz : z ∈ Metric.sphere s (ε/2)) :
      ‖regularSeries f c z‖ ≤ K*2^(2*ε)*((D+1)*(‖s‖+2))^(2*ε) := by
    have hdist := Metric.mem_sphere.mp hz
    have hzR := hre z hdist.le
    have hnorm : ‖z‖+2 ≤ 2*(‖s‖+2) := by
      have : ‖z‖ ≤ dist z s + ‖s‖ := by simpa [dist_eq_norm] using norm_add_le (z-s) s
      rw [hdist] at this
      nlinarith [norm_nonneg s]
    calc
      _ ≤ K*((D+1)*(‖z‖+2))^(2*ε) := h f c D hf0 hf hc hD hb z hzR
      _ ≤ K*(2*((D+1)*(‖s‖+2)))^(2*ε) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by nlinarith) (by positivity)) hK.le
      _ = _ := by rw [Real.mul_rpow (by positivity) (by positivity)]; ring
  have hder := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hε2 hd hbnd
  convert hder using 1
  all_goals try with_reducible_and_instances rfl
  ring

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIQ083_JD.PrimeGaps_TaylorBounds
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

open scoped ComplexConjugate

open Filter Topology

open Complex Filter Topology

open Complex Filter Topology Set MeasureTheory Asymptotics

open Finset

open Complex Filter Topology Finset

lemma power_series_tail_bound {a : ℕ → ℝ} {M r z : ℝ} (_hM : 0 ≤ M)
    (hr : 0 < r) (hz : 0 ≤ z) (hzr : z < r)
    (hb : ∀ n, |a n| ≤ M/r^n) (N : ℕ) :
    |∑' n : ℕ, a (n+N)*z^(n+N)| ≤ M*(z/r)^N/(1-z/r) := by
  have hρ : 0 ≤ z/r := div_nonneg hz hr.le
  have hρ1 : z/r < 1 := (div_lt_one hr).mpr hzr
  have hg := (summable_geometric_of_lt_one hρ hρ1).mul_left (M*(z/r)^N)
  have hbound (n : ℕ) : ‖a (n+N)*z^(n+N)‖ ≤ (M*(z/r)^N)*(z/r)^n := by
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (pow_nonneg hz _)]
    calc
      _ ≤ (M/r^(n+N))*z^(n+N) := mul_le_mul_of_nonneg_right (hb _) (pow_nonneg hz _)
      _ = M*(z/r)^(n+N) := by rw [div_pow]; ring
      _ = _ := by rw [pow_add]; ring
  have hn := hg.of_nonneg_of_le (fun n => norm_nonneg _) hbound
  calc
    _ = ‖∑' n : ℕ, a (n+N)*z^(n+N)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' n : ℕ, ‖a (n+N)*z^(n+N)‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' n : ℕ, (M*(z/r)^N)*(z/r)^n := hn.tsum_le_tsum hbound hg
    _ = _ := by rw [tsum_mul_left,tsum_geometric_of_lt_one hρ hρ1]; rfl

lemma residue_lower_bound_of_taylor {a : ℕ → ℝ} {R M r z : ℝ} {N : ℕ}
    (hM : 0 ≤ M) (hr : 0 < r) (hz : 1 < z) (hzr : z < r)
    (hb : ∀ n, |a n| ≤ M/r^n) (ha0 : 1-R ≤ a 0)
    (ha : ∀ n, -R ≤ a n) (hN : 1 ≤ N)
    (hvalue : (∑' n : ℕ, a n*z^n) ≤ R/(z-1))
    (htail : M*(z/r)^N/(1-z/r) ≤ 1/2) :
    (z-1)/2 ≤ R*z^N := by
  have heach : ∀ n, (if n=0 then 1 else (0:ℝ)) - R*z^n ≤ a n*z^n := by
    intro n
    by_cases hn : n=0
    · simpa [hn] using ha0
    · simp only [hn,↓reduceIte,zero_sub]
      nlinarith [mul_le_mul_of_nonneg_right (ha n) (pow_nonneg (zero_lt_one.trans hz).le n)]
  have hsum := Finset.sum_le_sum (s := range N) (fun n _ => heach n)
  have hzero : (∑ n ∈ range N, if n=0 then 1 else (0:ℝ)) = 1 := by
    simp [show 0 < N by omega]
  rw [sum_sub_distrib,hzero,←mul_sum] at hsum
  have htail' := power_series_tail_bound hM hr (zero_lt_one.trans hz).le hzr hb N
  have ht : -(1/2:ℝ) ≤ ∑' n : ℕ, a (n+N)*z^(n+N) := by
    have := (abs_le.mp (htail'.trans htail)).1
    linarith
  have hs : Summable (fun n : ℕ => a n*z^n) := by
    have hρ : 0 ≤ z/r := by positivity
    have hρ1 : z/r < 1 := (div_lt_one hr).mpr hzr
    apply ((summable_geometric_of_lt_one hρ hρ1).mul_left M).of_norm_bounded
    intro n
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (pow_nonneg (zero_lt_one.trans hz).le _)]
    calc
      _ ≤ (M/r^n)*z^n := mul_le_mul_of_nonneg_right (hb _) (pow_nonneg (zero_lt_one.trans hz).le _)
      _ = M*(z/r)^n := by rw [div_mul_eq_mul_div,div_pow]; ring
  have hdecomp := hs.sum_add_tsum_nat_add N
  have hm : 1/2 ≤ R/(z-1)+R*(∑ n ∈ range N, z^n) := by linarith
  have hgeom := geom_sum_mul z N
  have hv := (le_div_iff₀ (sub_pos.mpr hz)).mp
    (show (1/2:ℝ) ≤ (R+R*(∑ n ∈ range N, z^n)*(z-1))/(z-1) from by
      rw [add_div,mul_div_cancel_right₀ _ (sub_pos.mpr hz).ne']
      exact hm)
  have hid : R+R*(∑ n ∈ range N, z^n)*(z-1) = R*z^N := by
    rw [mul_assoc R, hgeom]
    ring
  rw [hid] at hv
  linarith

lemma signedTaylorCoeff_hasSum {H : ℂ → ℂ} {r z : ℝ}
    (hf : DifferentiableOn ℂ H (Metric.ball 2 r)) (hz : |z| < r) :
    HasSum (fun n => signedTaylorCoeff H n*z^n) (H ((2-z:ℝ):ℂ)).re := by
  have hmem : ((2-z:ℝ):ℂ) ∈ Metric.ball (2:ℂ) r := by
    rw [Metric.mem_ball,dist_eq_norm]
    have he : ((2-z:ℝ):ℂ)-(2:ℂ) = -(z:ℂ) := by push_cast <;> ring
    simpa [he,Complex.norm_real,Real.norm_eq_abs] using hz
  have hs := (Complex.hasSum_taylorSeries_on_ball hf hmem).map Complex.reCLM Complex.continuous_re
  change HasSum (fun n => ((n.factorial:ℂ)⁻¹ *
    ((((2-z:ℝ):ℂ)-2)^n * iteratedDeriv n H 2)).re) (H ((2-z:ℝ):ℂ)).re at hs
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  dsimp [signedTaylorCoeff]
  have he : ((2-z:ℝ):ℂ)-(2:ℂ) = -(z:ℂ) := by push_cast <;> ring
  rw [he, show (-(z:ℂ))^n = (-1:ℂ)^n * (z:ℂ)^n by rw [←mul_pow]; congr 1; ring]
  have hmul : (n.factorial:ℂ)⁻¹*((-1:ℂ)^n*(z:ℂ)^n*iteratedDeriv n H 2) =
      ((-1:ℂ)^n*(n.factorial:ℂ)⁻¹*iteratedDeriv n H 2)*(z:ℂ)^n := by ring
  rw [hmul]
  simp only [←Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    mul_zero,sub_zero]

lemma signedTaylorCoeff_norm_bound {H : ℂ → ℂ} {r M : ℝ} (hr : 0 < r)
    (hf : DiffContOnCl ℂ H (Metric.ball 2 r))
    (hb : ∀ s ∈ Metric.sphere 2 r, ‖H s‖ ≤ M) (n : ℕ) :
    |signedTaylorCoeff H n| ≤ M/r^n := by
  have hder := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr hf hb
  have hfact : (n.factorial:ℝ) ≠ 0 := by positivity
  calc
    _ ≤ ‖(-1:ℂ)^n*(n.factorial:ℂ)⁻¹*iteratedDeriv n H 2‖ := Complex.abs_re_le_norm _
    _ = (n.factorial:ℝ)⁻¹*‖iteratedDeriv n H 2‖ := by simp [norm_pow]
    _ ≤ (n.factorial:ℝ)⁻¹*((n.factorial:ℝ)*M/r^n) := by gcongr
    _ = _ := by field_simp

lemma signedTaylorCoeff_pole (R : ℝ) (n : ℕ) :
    signedTaylorCoeff (fun s : ℂ => (R:ℂ)/(s-1)) n = R := by
  unfold signedTaylorCoeff
  simp only [div_eq_mul_inv,iteratedDeriv_const_mul_field]
  have hi : iteratedDeriv n (fun s : ℂ => (s-1)⁻¹) 2 = (-1:ℂ)^n*n.factorial := by
    rw [iteratedDeriv_eq_iterate]
    simpa only [one_mul,one_pow, show (2:ℂ)-1=1 by norm_num, one_zpow,mul_one] using
      congrFun (iter_deriv_inv_linear_sub n (1:ℂ) 1) 2
  rw [hi]
  have hf : (n.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hp : (-1:ℂ)^n*(-1:ℂ)^n = 1 := by rw [←mul_pow]; simp
  have he : (-1:ℂ)^n*(n.factorial:ℂ)⁻¹*((R:ℂ)*((-1:ℂ)^n*n.factorial)) = R := by
    calc
      _ = ((-1:ℂ)^n*(-1:ℂ)^n)*(R:ℂ)*((n.factorial:ℂ)⁻¹*n.factorial) := by ring
      _ = _ := by rw [hp,inv_mul_cancel₀ hf]; ring
  rw [he,Complex.ofReal_re]

lemma signedTaylorCoeff_sub {F G : ℂ → ℂ} (hF : AnalyticAt ℂ F 2)
    (hG : AnalyticAt ℂ G 2) (n : ℕ) :
    signedTaylorCoeff (fun s => F s-G s) n = signedTaylorCoeff F n-signedTaylorCoeff G n := by
  unfold signedTaylorCoeff
  have hd := iteratedDeriv_sub (n:=n) hF.contDiffAt hG.contDiffAt
  change iteratedDeriv n (fun s => F s-G s) 2 = _ at hd
  rw [hd,mul_sub,Complex.sub_re]

open scoped ComplexOrder in
lemma signedTaylorCoeff_LSeries_nonneg {a : ℕ → ℂ} (ha : ∀ n, 0 ≤ a n)
    (hc : LSeries.abscissaOfAbsConv a < (2:ℝ)) (n : ℕ) :
    0 ≤ signedTaylorCoeff (LSeries a) n := by
  have h := LSeries.iteratedDeriv_alternating ha hc n
  have hf : (0:ℝ) ≤ (n.factorial:ℝ)⁻¹ := by positivity
  have hr := (Complex.nonneg_iff.mp h).1
  unfold signedTaylorCoeff
  have he : (-1:ℂ)^n*(n.factorial:ℂ)⁻¹*iteratedDeriv n (LSeries a) 2 =
      (n.factorial:ℂ)⁻¹*((-1:ℂ)^n*iteratedDeriv n (LSeries a) 2) := by ring
  rw [he]
  simpa using mul_nonneg hf hr

open scoped ComplexOrder in
lemma LSeries_two_re_ge_one {a : ℕ → ℂ} (ha : ∀ n, 0 ≤ a n)
    (ha1 : 1 ≤ a 1) (hc : LSeries.abscissaOfAbsConv a < (2:ℝ)) :
    1 ≤ (LSeries a 2).re := by
  have hs : LSeriesSummable a 2 := LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using hc)
  have hl := hs.le_tsum 1 (fun n _ => LSeries.term_nonneg (ha n) 2)
  have hterm : LSeries.term a 2 1 = a 1 := by simp
  rw [hterm] at hl
  exact (Complex.le_def.mp (ha1.trans hl)).1

open scoped ComplexOrder in
lemma signedTaylorCoeff_regular_nonneg {H : ℂ → ℂ} {a : ℕ → ℂ} {R : ℝ}
    (ha : ∀ n, 0 ≤ a n) (ha1 : 1 ≤ a 1)
    (hc : LSeries.abscissaOfAbsConv a < (2:ℝ))
    (he : H =ᶠ[𝓝 (2:ℂ)] fun s => LSeries a s-(R:ℂ)/(s-1)) :
    1-R ≤ (H 2).re ∧ ∀ n, -R ≤ signedTaylorCoeff H n := by
  have hL : AnalyticAt ℂ (LSeries a) 2 := LSeries_analyticOnNhd a 2 (by simpa using hc)
  have hP : AnalyticAt ℂ (fun s : ℂ => (R:ℂ)/(s-1)) 2 :=
    analyticAt_const.div (analyticAt_id.sub analyticAt_const) (by norm_num)
  constructor
  · rw [he.self_of_nhds]
    have h := LSeries_two_re_ge_one ha ha1 hc
    simp only [show (2:ℂ)-1=1 by norm_num,div_one,Complex.sub_re,Complex.ofReal_re]
    linarith
  · intro n
    unfold signedTaylorCoeff
    rw [he.iteratedDeriv_eq]
    change -R ≤ signedTaylorCoeff (fun s => LSeries a s-(R:ℂ)/(s-1)) n
    rw [signedTaylorCoeff_sub hL hP,signedTaylorCoeff_pole]
    linarith [signedTaylorCoeff_LSeries_nonneg ha hc n]

lemma residue_polynomial_lower {a : ℕ → ℝ} {R A Q z ε : ℝ}
    (hA : 0 ≤ A) (hQ : 2 ≤ Q) (hQA : 12*A ≤ Q)
    (hz : 1 < z) (hz1 : z ≤ 5/4) (hzε : 60*(z-1) ≤ ε)
    (hb : ∀ n, |a n| ≤ (A*Q^4)/(3/2)^n)
    (ha0 : 1-R ≤ a 0) (ha : ∀ n, -R ≤ a n)
    (hv : (∑' n : ℕ, a n*z^n) ≤ R/(z-1)) :
    ((z-1)/(2*z))*Q^(-ε) ≤ R := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hlogQ : 0 < Real.log Q := Real.log_pos (by linarith)
  have hz0 : 0 < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos hz
  let N : ℕ := ⌈60*Real.log Q⌉₊
  have hNlo : 60*Real.log Q ≤ (N:ℝ) := Nat.le_ceil _
  have hNhi : (N:ℝ) < 60*Real.log Q+1 := Nat.ceil_lt_add_one (by positivity)
  have hN : 1 ≤ N := by
    have : 0 < (N:ℝ) := lt_of_lt_of_le (by positivity) hNlo
    exact_mod_cast (show 1 ≤ N from Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast this.ne'))
  have hρ : 0 ≤ z/(3/2) := by positivity
  have hρ1 : z/(3/2) ≤ 5/6 := by linarith
  have hlogρ : Real.log (5/6:ℝ) ≤ -(1/6:ℝ) := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 5/6)
    linarith
  have hdecay : (z/(3/2))^N ≤ Q^(-10:ℝ) := by
    calc
      _ ≤ (5/6:ℝ)^N := pow_le_pow_left₀ hρ hρ1 N
      _ = Real.exp (Real.log (5/6:ℝ)*(N:ℝ)) := by
        rw [←Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 5/6)]
      _ ≤ Real.exp (Real.log Q*(-10)) := by
        apply Real.exp_le_exp.mpr
        have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
        nlinarith [mul_le_mul_of_nonneg_right hlogρ hN0]
      _ = _ := (Real.rpow_def_of_pos hQ0 _).symm
  have htail : (A*Q^4)*(z/(3/2))^N/(1-z/(3/2)) ≤ 1/2 := by
    have hden : 0 < 1-z/(3/2) := by linarith
    have hpow : Q^4*Q^(-10:ℝ) ≤ Q⁻¹ := by
      calc
        _ = Q^(-6:ℝ) := by
          rw [←Real.rpow_natCast,←Real.rpow_add hQ0]
          norm_num
        _ ≤ Q^(-1:ℝ) := Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)
        _ = Q⁻¹ := Real.rpow_neg_one Q
    have hp : (A*Q^4)*(z/(3/2))^N ≤ A/Q := by
      calc
        _ ≤ (A*Q^4)*Q^(-10:ℝ) := mul_le_mul_of_nonneg_left hdecay (by positivity)
        _ ≤ A*Q⁻¹ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hpow hA
        _ = _ := by rw [div_eq_mul_inv]
    have hAQ : A/Q ≤ 1/12 := (div_le_iff₀ hQ0).mpr (by linarith)
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hres := residue_lower_bound_of_taylor (by positivity : (0:ℝ) ≤ A*Q^4)
    (by norm_num : (0:ℝ) < 3/2) hz (by linarith : z < 3/2) hb ha0 ha hN hv htail
  have hzpow : z^N ≤ z*Q^ε := by
    have hlogz' : 60*Real.log z ≤ ε := by
      have := Real.log_le_sub_one_of_pos hz0
      linarith
    calc
      _ = Real.exp (Real.log z*(N:ℝ)) := by rw [←Real.rpow_natCast,Real.rpow_def_of_pos hz0]
      _ ≤ Real.exp (Real.log z+(Real.log Q)*ε) := by
        apply Real.exp_le_exp.mpr
        have h1 := mul_le_mul_of_nonneg_left hNhi.le hlogz.le
        have h2 := mul_le_mul_of_nonneg_left hlogz' hlogQ.le
        nlinarith
      _ = _ := by rw [Real.exp_add,Real.exp_log hz0,Real.rpow_def_of_pos hQ0]
  have hR : 0 ≤ R := by
    by_contra! h
    have := mul_neg_of_neg_of_pos h (pow_pos hz0 N)
    linarith
  have hres' : (z-1)/2 ≤ R*(z*Q^ε) := hres.trans (mul_le_mul_of_nonneg_left hzpow hR)
  rw [Real.rpow_neg hQ0.le,←div_eq_mul_inv]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hQ0 ε)).mpr
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*z)).mpr
  nlinarith

open Complex Filter Topology Finset Set MeasureTheory

lemma zetaRegular_differentiableAt {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ zetaRegular s :=
  regularSeries_differentiableAt zero_le_one (fun _ ht => discrepancy_constant_bound ht.le) hs

lemma zetaRegular_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    zetaRegular s = riemannZeta s-1/(s-1) := by
  rw [zetaRegular,regularSeries_eq_LSeries_sub (positiveCoefficients_norm_le (by simp))
    zero_le_one (fun _ ht => discrepancy_constant_bound ht.le) hs,LSeries_positiveCoefficients]
  rw [show (fun _ : ℕ => (1:ℂ)) = 1 from rfl,LSeries_one_eq_riemannZeta hs]

lemma poleRemovedZeta_eq {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunctionTrivChar₁ 1 s = (s-1)*zetaRegular s+1 := by
  have hF : AnalyticOnNhd ℂ (DirichletCharacter.LFunctionTrivChar₁ 1) {s : ℂ | 0 < s.re} :=
    fun z _ => (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1).analyticAt z
  have hG : AnalyticOnNhd ℂ (fun s : ℂ => (s-1)*zetaRegular s+1) {s : ℂ | 0 < s.re} := by
    apply DifferentiableOn.analyticOnNhd ?_ (continuous_re.isOpen_preimage _ isOpen_Ioi)
    intro z hz
    exact (((differentiableAt_id.sub_const 1).mul (zetaRegular_differentiableAt hz)).add_const 1).differentiableWithinAt
  have he : DirichletCharacter.LFunctionTrivChar₁ 1 =ᶠ[𝓝 (2:ℂ)]
      fun s : ℂ => (s-1)*zetaRegular s+1 := by
    filter_upwards [(continuous_re.tendsto (2:ℂ)).eventually
      (lt_mem_nhds (by norm_num : (1:ℝ) < (2:ℂ).re))] with z hz
    have hz1 : z ≠ 1 := by intro h; simp [h] at hz
    rw [DirichletCharacter.LFunctionTrivChar₁,Function.update_of_ne hz1,
      DirichletCharacter.LFunctionTrivChar,DirichletCharacter.LFunction_modOne_eq,
      zetaRegular_eq_of_one_lt_re hz]
    field_simp
    ring
  exact hF.eqOn_of_preconnected_of_eventuallyEq hG (convex_halfSpace_re_gt 0).isPreconnected
    (show (2:ℂ) ∈ {s : ℂ | 0 < s.re} by norm_num) he hs

lemma zetaRegular_eq {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    zetaRegular s = riemannZeta s-1/(s-1) := by
  have h := poleRemovedZeta_eq hs
  rw [DirichletCharacter.LFunctionTrivChar₁,Function.update_of_ne hs1,
    DirichletCharacter.LFunctionTrivChar,DirichletCharacter.LFunction_modOne_eq] at h
  have hn : s-1 ≠ 0 := sub_ne_zero.mpr hs1
  apply (mul_left_cancel₀ hn)
  rw [mul_sub,mul_div_cancel₀ _ hn]
  linear_combination -h

lemma regularSeries_norm_simple {f : ℕ → ℂ} {c : ℂ} {D : ℝ} (hD : 0 ≤ D)
    (hb : ∀ t, 1 < t → ‖seriesDiscrepancy f c t‖ ≤ D) {s : ℂ} (hs : 0 < s.re) :
    ‖regularSeries f c s‖ ≤ ‖c‖+‖s‖*D/s.re := by
  have h := discrepancyTail_norm_le zero_lt_one hD (measurable_seriesDiscrepancy f c) hb hs
  simp only [Real.one_rpow,mul_one] at h
  calc
    _ ≤ ‖c‖+‖s*discrepancyTail (seriesDiscrepancy f c) 1 s‖ := norm_add_le _ _
    _ ≤ ‖c‖+‖s‖*(D/s.re) := by rw [norm_mul]; gcongr
    _ = _ := by ring

lemma closedBall_two_re_norm {s : ℂ} (hs : s ∈ Metric.closedBall 2 (7/4:ℝ)) :
    (1/4:ℝ) ≤ s.re ∧ ‖s‖ ≤ 4 := by
  have hd := Metric.mem_closedBall.mp hs
  have hr := Complex.re_le_norm ((2:ℂ)-s)
  rw [Complex.sub_re,←dist_eq_norm,dist_comm] at hr
  have hn : ‖s‖ ≤ dist s 2+‖(2:ℂ)‖ := by simpa [dist_eq_norm] using norm_add_le (s-2) (2:ℂ)
  norm_num at hr hn
  constructor <;> linarith

lemma zetaRegular_norm_le_seventeen {s : ℂ} (hs : s ∈ Metric.closedBall 2 (7/4:ℝ)) :
    ‖zetaRegular s‖ ≤ 17 := by
  obtain ⟨hre,hnorm⟩ := closedBall_two_re_norm hs
  have hp : 0 < s.re := by linarith
  have h := regularSeries_norm_simple zero_le_one (fun _ ht => discrepancy_constant_bound ht.le) hp
  change ‖zetaRegular s‖ ≤ _ at h
  norm_num at h
  have hq : ‖s‖/s.re ≤ 16 := (div_le_iff₀ hp).mpr (by linarith)
  linarith

lemma LFunction_norm_polynomial {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hs : s ∈ Metric.closedBall 2 (7/4:ℝ)) :
    ‖χ.LFunction s‖ ≤ 16*((q:ℝ)+1) := by
  obtain ⟨hre,hnorm⟩ := closedBall_two_re_norm hs
  have hp : 0 < s.re := by linarith
  have hb := regularSeries_norm_simple (by positivity : (0:ℝ) ≤ q+1)
    (fun t _ => discrepancy_character_bound hχ t) hp
  rw [regularSeries_character_eq hχ hp] at hb
  simp only [norm_zero,zero_add] at hb
  apply hb.trans
  apply (div_le_iff₀ hp).mpr
  nlinarith [Nat.cast_nonneg (α:=ℝ) q]

lemma regularizedZetaProduct_differentiableOn {P : ℂ → ℂ}
    (hP : DifferentiableOn ℂ P {s : ℂ | 0 < s.re}) :
    DifferentiableOn ℂ (regularizedZetaProduct P) {s : ℂ | 0 < s.re} := by
  have hs : {s : ℂ | 0 < s.re} ∈ 𝓝 (1:ℂ) :=
    (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by norm_num)
  have hd := (Complex.differentiableOn_dslope hs).mpr hP
  have hz : DifferentiableOn ℂ zetaRegular {s : ℂ | 0 < s.re} :=
    fun s hs => (zetaRegular_differentiableAt hs).differentiableWithinAt
  exact (hz.mul hP).add hd

lemma regularizedZetaProduct_eq {P : ℂ → ℂ} {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    regularizedZetaProduct P s = riemannZeta s*P s-P 1/(s-1) := by
  rw [regularizedZetaProduct,zetaRegular_eq hs hs1,dslope_of_ne P hs1,slope_def_field]
  ring

lemma regularizedZetaProduct_bound {P : ℂ → ℂ} {B : ℝ}
    (hP : DifferentiableOn ℂ P {s : ℂ | 0 < s.re}) (_hB : 0 ≤ B)
    (hb : ∀ s ∈ Metric.closedBall (2:ℂ) (7/4:ℝ), ‖P s‖ ≤ B) :
    DiffContOnCl ℂ (regularizedZetaProduct P) (Metric.ball 2 (3/2:ℝ)) ∧
      ∀ s ∈ Metric.closedBall (2:ℂ) (3/2:ℝ), ‖regularizedZetaProduct P s‖ ≤ 21*B := by
  have hsRe (s : ℂ) (hs : s ∈ Metric.closedBall 2 (7/4:ℝ)) : 0 < s.re := by
    have := (closedBall_two_re_norm hs).1
    linarith
  have hder (s : ℂ) (hs : s ∈ Metric.closedBall 2 (3/2:ℝ)) : ‖deriv P s‖ ≤ 4*B := by
    have hsub : Metric.closedBall s (1/4:ℝ) ⊆ Metric.closedBall (2:ℂ) (7/4:ℝ) := by
      intro z hz
      have hdist := dist_triangle z s (2:ℂ)
      have hz' := Metric.mem_closedBall.mp hz
      have hs' := Metric.mem_closedBall.mp hs
      apply Metric.mem_closedBall.mpr
      linarith
    have hdiff : DiffContOnCl ℂ P (Metric.ball s (1/4:ℝ)) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball _ (by norm_num : (1/4:ℝ) ≠ 0)]
      exact hP.mono (fun z hz => hsRe z (hsub hz))
    have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0:ℝ) < 1/4)
      hdiff (fun z hz => hb z (hsub (Metric.sphere_subset_closedBall hz)))
    convert h using 1 <;> first | rfl | ring
  have hone : (1:ℂ) ∈ Metric.closedBall (2:ℂ) (3/2:ℝ) := by
    norm_num [Metric.mem_closedBall,dist_eq_norm]
  have hdslope (s : ℂ) (hs : s ∈ Metric.closedBall 2 (3/2:ℝ)) : ‖dslope P 1 s‖ ≤ 4*B := by
    by_cases hs1 : s = 1
    · subst s
      simpa only [dslope_same] using hder 1 hone
    · rw [dslope_of_ne P hs1,slope_def_field,norm_div]
      have hd := (convex_closedBall (2:ℂ) (3/2:ℝ)).norm_image_sub_le_of_norm_deriv_le
        (fun z hz => (hP z (hsRe z (Metric.closedBall_subset_closedBall (by norm_num) hz))).differentiableAt
          ((continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
            (hsRe z (Metric.closedBall_subset_closedBall (by norm_num) hz)))) hder hone hs
      exact (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hs1))).mpr hd
  constructor
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ (by norm_num : (3/2:ℝ) ≠ 0)]
    exact (regularizedZetaProduct_differentiableOn hP).mono
      (fun z hz => hsRe z (Metric.closedBall_subset_closedBall (by norm_num) hz))
  · intro s hs
    have hs' := Metric.closedBall_subset_closedBall (by norm_num : (3/2:ℝ) ≤ 7/4) hs
    calc
      _ ≤ ‖zetaRegular s*P s‖+‖dslope P 1 s‖ := norm_add_le _ _
      _ ≤ 17*B+4*B := by rw [norm_mul]; gcongr; exact zetaRegular_norm_le_seventeen hs'; exact hb s hs'; exact hdslope s hs
      _ = _ := by ring

open Complex Finset ArithmeticFunction

open scoped ComplexOrder

lemma PrimePowerEq.refl (p : ℕ) (f : ArithmeticFunction ℂ) : PrimePowerEq p f f := fun _ => rfl

lemma PrimePowerEq.mul {p : ℕ} (hp : p.Prime) {f f' g g' : ArithmeticFunction ℂ}
    (hf : PrimePowerEq p f f') (hg : PrimePowerEq p g g') : PrimePowerEq p (f*g) (f'*g') := by
  intro k
  simp only [ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨i,hi,hxi⟩ := (Nat.dvd_prime_pow hp).mp (Nat.mem_divisors.mp
    (Nat.fst_mem_divisors_of_mem_antidiagonal hx)).1
  obtain ⟨j,hj,hxj⟩ := (Nat.dvd_prime_pow hp).mp (Nat.mem_divisors.mp
    (Nat.snd_mem_divisors_of_mem_antidiagonal hx)).1
  rw [hxi,hxj,hf,hg]

lemma primePower_zeta {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (ArithmeticFunction.zeta : ArithmeticFunction ℂ) (p^k) = 1 := by
  simp [hp.ne_zero]

lemma primePower_one {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (1 : ArithmeticFunction ℂ) (p^k) = (0:ℂ)^k := by
  cases k with
  | zero => simp
  | succ k =>
    have hn : p^(k+1) ≠ 1 := by
      have h : 1 < p^(k+1) := one_lt_pow₀ hp.one_lt (by omega)
      omega
    simp [hp.ne_one]

lemma primePower_character {q p : ℕ} (χ : DirichletCharacter ℂ q) (hp : p.Prime) (k : ℕ) :
    toArithmeticFunction (χ ·) (p^k) = χ (p : ZMod q)^k := by
  simp [toArithmeticFunction,hp.ne_zero]

lemma arithmetic_convolution_nonneg {f g : ArithmeticFunction ℂ}
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (n : ℕ) : 0 ≤ (f*g) n := by
  rw [ArithmeticFunction.mul_apply]
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (hf x.1) (hg x.2))

lemma biquadraticCoefficients_multiplicative {q r : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) :
    (biquadraticCoefficients χ ψ).IsMultiplicative := by
  exact ((isMultiplicative_zeta.natCast.mul (DirichletCharacter.isMultiplicative_toArithmeticFunction χ)).mul
    (DirichletCharacter.isMultiplicative_toArithmeticFunction ψ)).mul
    ((DirichletCharacter.isMultiplicative_toArithmeticFunction χ).pmul (DirichletCharacter.isMultiplicative_toArithmeticFunction ψ))

lemma biquadraticCoefficients_comm {q r : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) :
    biquadraticCoefficients χ ψ = biquadraticCoefficients ψ χ := by
  unfold biquadraticCoefficients
  rw [ArithmeticFunction.pmul_comm]
  ring

lemma biquadratic_prime_zero {q r p : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) (hp : p.Prime)
    (hχ : χ (p : ZMod q) = 0) :
    PrimePowerEq p (biquadraticCoefficients χ ψ) ψ.zetaMul := by
  have hf : PrimePowerEq p (toArithmeticFunction (χ ·)) 1 := by
    intro k
    rw [primePower_character χ hp, hχ,primePower_one hp]
  have hh : PrimePowerEq p ((toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·))) 1 := by
    intro k
    rw [ArithmeticFunction.pmul_apply,primePower_character χ hp,primePower_character ψ hp,
      hχ,←mul_pow,zero_mul,primePower_one hp]
  have h := ((PrimePowerEq.refl p (ArithmeticFunction.zeta : ArithmeticFunction ℂ)).mul hp hf).mul hp
    (PrimePowerEq.refl p (toArithmeticFunction (ψ ·))) |>.mul hp hh
  simpa only [mul_one,biquadraticCoefficients,DirichletCharacter.zetaMul] using h

lemma biquadratic_prime_one {q r p : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) (hp : p.Prime)
    (hχ : χ (p : ZMod q) = 1) :
    PrimePowerEq p (biquadraticCoefficients χ ψ) (ψ.zetaMul*ψ.zetaMul) := by
  have hf : PrimePowerEq p (toArithmeticFunction (χ ·)) ArithmeticFunction.zeta := by
    intro k
    rw [primePower_character χ hp,hχ,one_pow,primePower_zeta hp]
  have hh : PrimePowerEq p ((toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·)))
      (toArithmeticFunction (ψ ·)) := by
    intro k
    rw [ArithmeticFunction.pmul_apply,primePower_character χ hp,hχ,one_pow,one_mul]
  have h := ((PrimePowerEq.refl p (ArithmeticFunction.zeta : ArithmeticFunction ℂ)).mul hp hf).mul hp
    (PrimePowerEq.refl p (toArithmeticFunction (ψ ·))) |>.mul hp hh
  have he : (ArithmeticFunction.zeta : ArithmeticFunction ℂ)*ArithmeticFunction.zeta*
      toArithmeticFunction (ψ ·)*toArithmeticFunction (ψ ·) = ψ.zetaMul*ψ.zetaMul := by
    unfold DirichletCharacter.zetaMul
    ring
  simpa only [he,biquadraticCoefficients] using h

lemma biquadratic_prime_neg_one {q r p : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) (hp : p.Prime)
    (hχ : χ (p : ZMod q) = -1) (hψ : ψ (p : ZMod r) = -1) :
    PrimePowerEq p (biquadraticCoefficients χ ψ) (χ.zetaMul*χ.zetaMul) := by
  have hg : PrimePowerEq p (toArithmeticFunction (ψ ·)) (toArithmeticFunction (χ ·)) := by
    intro k
    rw [primePower_character ψ hp,primePower_character χ hp,hχ,hψ]
  have hh : PrimePowerEq p ((toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·)))
      ArithmeticFunction.zeta := by
    intro k
    rw [ArithmeticFunction.pmul_apply,primePower_character χ hp,primePower_character ψ hp,
      hχ,hψ,←mul_pow,neg_mul_neg,one_mul,one_pow,primePower_zeta hp]
  have h := ((PrimePowerEq.refl p (ArithmeticFunction.zeta : ArithmeticFunction ℂ)).mul hp
    (PrimePowerEq.refl p (toArithmeticFunction (χ ·)))).mul hp hg |>.mul hp hh
  have he : (ArithmeticFunction.zeta : ArithmeticFunction ℂ)*toArithmeticFunction (χ ·)*
      toArithmeticFunction (χ ·)*ArithmeticFunction.zeta = χ.zetaMul*χ.zetaMul := by
    unfold DirichletCharacter.zetaMul
    ring
  simpa only [he,biquadraticCoefficients] using h

lemma biquadraticCoefficients_nonneg {q r : ℕ} {χ : DirichletCharacter ℂ q}
    {ψ : DirichletCharacter ℂ r} (hχ : χ^2=1) (hψ : ψ^2=1) (n : ℕ) :
    0 ≤ biquadraticCoefficients χ ψ n := by
  have hp (p : ℕ) (hp : p.Prime) (k : ℕ) : 0 ≤ biquadraticCoefficients χ ψ (p^k) := by
    rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ (p:ZMod q) with h0|h1|hm
    · rw [biquadratic_prime_zero χ ψ hp h0 k]
      exact DirichletCharacter.zetaMul_nonneg hψ _
    · rw [biquadratic_prime_one χ ψ hp h1 k]
      exact arithmetic_convolution_nonneg (DirichletCharacter.zetaMul_nonneg hψ)
        (DirichletCharacter.zetaMul_nonneg hψ) _
    · rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hψ (p:ZMod r) with h0|h1|hm'
      · rw [biquadraticCoefficients_comm χ ψ,biquadratic_prime_zero ψ χ hp h0 k]
        exact DirichletCharacter.zetaMul_nonneg hχ _
      · rw [biquadraticCoefficients_comm χ ψ,biquadratic_prime_one ψ χ hp h1 k]
        exact arithmetic_convolution_nonneg (DirichletCharacter.zetaMul_nonneg hχ)
          (DirichletCharacter.zetaMul_nonneg hχ) _
      · rw [biquadratic_prime_neg_one χ ψ hp hm hm' k]
        exact arithmetic_convolution_nonneg (DirichletCharacter.zetaMul_nonneg hχ)
          (DirichletCharacter.zetaMul_nonneg hχ) _
  rcases eq_or_ne n 0 with rfl|hn
  · simp
  · simpa only [(biquadraticCoefficients_multiplicative χ ψ).multiplicative_factorization _ hn,
      Finsupp.prod, Nat.support_factorization] using
      Finset.prod_nonneg (fun p hp' => hp p (Nat.prime_of_mem_primeFactors hp') _)

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIQ083_JD.PrimeGaps_SiegelBounds
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

section

open Complex Filter Topology Set MeasureTheory Finset ArithmeticFunction

lemma quadratic_character_im {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ^2=1)
    (a : ZMod q) : (χ a).im = 0 := by
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ a with h|h|h <;> simp [h]

lemma regularSeries_im_zero {f : ℕ → ℂ} {c : ℂ} {D : ℝ}
    (hf : ∀ n, (f n).im=0) (hc : c.im=0) (hD : 0 ≤ D)
    (hb : ∀ t, 1<t → ‖seriesDiscrepancy f c t‖ ≤ D) {x : ℝ} (hx : 0<x) :
    (regularSeries f c x).im=0 := by
  have hi := discrepancyTail_integrable zero_lt_one hD (measurable_seriesDiscrepancy f c) hb
    (show 0<(x:ℂ).re from hx)
  have he : (discrepancyTail (seriesDiscrepancy f c) 1 x).im=0 := by
    unfold discrepancyTail
    change RCLike.im (∫ t in Ioi (1:ℝ), seriesDiscrepancy f c t*(t:ℂ)^(-((x:ℂ)+1)))=0
    rw [←integral_im hi]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hp : ((t:ℂ)^(-((x:ℂ)+1))).im=0 := by
      rw [show -((x:ℂ)+1)= (-(x+1):ℝ) by push_cast; rfl,
        ←Complex.ofReal_cpow (by exact (zero_lt_one.trans ht).le : 0≤t)]
      rfl
    change (seriesDiscrepancy f c t * (t:ℂ)^(-((x:ℂ)+1))).im=0
    rw [Complex.mul_im,hp,mul_zero,zero_add]
    have hz : (seriesDiscrepancy f c t).im=0 := by simp [seriesDiscrepancy,Complex.mul_im,hc,hf]
    rw [hz,zero_mul]
  simp [regularSeries,Complex.mul_im,hc,he]

lemma quadratic_LFunction_im {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) (hχ2 : χ^2=1) {x : ℝ} (hx : 0<x) : (χ.LFunction x).im=0 := by
  rw [←regularSeries_character_eq hχ hx]
  apply regularSeries_im_zero _ (by simp) (by positivity : (0:ℝ)≤q+1)
    (fun t _ => discrepancy_character_bound hχ t) hx
  intro n
  simp only [positiveCoefficients]
  split_ifs <;> simp [quadratic_character_im hχ2]

lemma LSeries_character_summable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (toArithmeticFunction (fun n : ℕ => χ (n : ZMod q))) s := by
  apply (LSeriesSummable_congr _ (fun h => (χ.apply_eq_toArithmeticFunction_apply h).symm)).mpr
  exact ZMod.LSeriesSummable_of_one_lt_re χ hs

lemma LSeries_character_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (toArithmeticFunction (fun n : ℕ => χ (n : ZMod q))) s = χ.LFunction s := by
  rw [χ.LFunction_eq_LSeries hs]
  exact (LSeries_congr χ.apply_eq_toArithmeticFunction_apply s).symm

lemma LSeries_zeta_complex_eq {s : ℂ} (hs : 1 < s.re) :
    LSeries (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s=riemannZeta s := by
  rw [←LSeries_one_eq_riemannZeta hs]
  apply LSeries_congr
  intro n hn
  simp [hn]

lemma LSeries_zetaMul_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) : LSeries χ.zetaMul s=riemannZeta s*χ.LFunction s := by
  have hz : LSeriesSummable (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s := by
    apply LSeriesSummable_of_bounded_of_one_lt_re (m:=1) _ hs
    intro n hn
    simp [hn]
  rw [DirichletCharacter.zetaMul,ArithmeticFunction.LSeries_mul' hz
    (LSeries_character_summable χ hs),LSeries_character_eq χ hs,LSeries_zeta_complex_eq hs]

open scoped ComplexOrder in
lemma quadratic_LFunction_re_pos_of_one_lt {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ2 : χ^2=1) {x : ℝ} (hx : 1<x) :
    0<(χ.LFunction x).re := by
  have hp := LSeries.positive (DirichletCharacter.zetaMul_nonneg hχ2)
    (χ.isMultiplicative_zetaMul.map_one ▸ zero_lt_one)
    (lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun s hs => χ.LSeriesSummable_zetaMul hs)) (show (1:EReal)<x by exact_mod_cast hx))
  rw [LSeries_zetaMul_eq χ hx] at hp
  have hr := (Complex.pos_iff.mp hp).1
  rw [Complex.mul_re,riemannZeta_im_eq_zero_of_one_lt hx,zero_mul,sub_zero] at hr
  exact (mul_pos_iff.mp hr).resolve_right (fun h => (riemannZeta_re_pos_of_one_lt hx).not_ge h.1.le) |>.2

lemma quadratic_LFunction_re_pos_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) (hχ2 : χ^2=1) : 0<(χ.LFunction 1).re := by
  have hc : Continuous (fun x : ℝ => (χ.LFunction x).re) :=
    Complex.continuous_re.comp ((DirichletCharacter.differentiable_LFunction hχ).continuous.comp
      Complex.continuous_ofReal)
  have hn : 0≤(χ.LFunction 1).re := by
    apply ge_of_tendsto (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
      Tendsto (fun x : ℝ => (χ.LFunction x).re) (𝓝[>] 1) (𝓝 ((χ.LFunction 1).re)))
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (quadratic_LFunction_re_pos_of_one_lt hχ2 hx).le
  refine lt_of_le_of_ne hn ?_
  intro he
  apply DirichletCharacter.LFunction_apply_one_ne_zero hχ
  apply Complex.ext
  · simpa using he.symm
  · simpa using quadratic_LFunction_im hχ hχ2 (x:=1) zero_lt_one

lemma quadratic_LFunction_re_pos_of_no_root {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ≠1) (hχ2 : χ^2=1)
    {β : ℝ} (hβ : 0<β) (hβ1 : β≤1)
    (hz : ∀ x ∈ Set.Icc β 1, χ.LFunction x≠0) : 0<(χ.LFunction β).re := by
  by_contra! hn
  have hc : Continuous (fun x : ℝ => (χ.LFunction x).re) :=
    Complex.continuous_re.comp ((DirichletCharacter.differentiable_LFunction hχ).continuous.comp
      Complex.continuous_ofReal)
  obtain ⟨x,hx,hxe⟩ := intermediate_value_Icc hβ1 hc.continuousOn
    (show (0:ℝ) ∈ Set.Icc ((χ.LFunction β).re) ((χ.LFunction 1).re) from
      ⟨hn,(quadratic_LFunction_re_pos_one hχ hχ2).le⟩)
  apply hz x hx
  apply Complex.ext
  · simpa using hxe
  · simpa using quadratic_LFunction_im hχ hχ2 (hβ.trans_le hx.1)

end

section

open Complex Finset ArithmeticFunction

lemma changeLevel_natCast {q m : ℕ} (χ : DirichletCharacter ℂ q) (hqm : q∣m)
    {n : ℕ} (hn : n.Coprime m) :
    χ.changeLevel hqm (n : ZMod m)=χ (n : ZMod q) := by
  have h := χ.changeLevel_eq_cast_of_dvd hqm (ZMod.unitOfCoprime n hn)
  simp only [ZMod.coe_unitOfCoprime] at h
  rw [ZMod.cast_natCast hqm] at h
  exact h

lemma productCharacter_apply {q r n : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) : productCharacter χ ψ (n : ZMod (q*r))=
      χ (n : ZMod q)*ψ (n : ZMod r) := by
  by_cases hn : n.Coprime (q*r)
  · simp only [productCharacter,MulChar.mul_apply,changeLevel_natCast _ _ hn]
  · rw [MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])]
    by_cases hq : n.Coprime q
    · have hr : ¬n.Coprime r := fun hr => hn (hq.mul_right hr)
      rw [ψ.map_nonunit (by rwa [ZMod.isUnit_iff_coprime]),mul_zero]
    · rw [χ.map_nonunit (by rwa [ZMod.isUnit_iff_coprime]),zero_mul]

lemma productCharacter_quadratic {q r : ℕ} {χ : DirichletCharacter ℂ q}
    {ψ : DirichletCharacter ℂ r} (hχ : χ^2=1) (hψ : ψ^2=1) :
    (productCharacter χ ψ)^2=1 := by
  simp [productCharacter,mul_pow,←map_pow,hχ,hψ]

lemma productCharacter_ne_one_of_levels_ne {q r : ℕ} [NeZero q] [NeZero r]
    {χ : DirichletCharacter ℂ q} {ψ : DirichletCharacter ℂ r}
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (hψ2 : ψ^2=1) (hqr : q≠r) :
    productCharacter χ ψ≠1 := by
  intro h
  have h2 : (ψ.changeLevel (dvd_mul_left r q))^2=1 := by rw [←map_pow,hψ2,map_one]
  have he : χ.changeLevel (dvd_mul_right q r) = ψ.changeLevel (dvd_mul_left r q) := by
    calc
      _ = (χ.changeLevel (dvd_mul_right q r)*ψ.changeLevel (dvd_mul_left r q))*
          ψ.changeLevel (dvd_mul_left r q) := by rw [mul_assoc,←pow_two,h2,mul_one]
      _ = _ := by rw [show χ.changeLevel (dvd_mul_right q r)*ψ.changeLevel (dvd_mul_left r q)=1 from h,one_mul]
  have hc := congrArg DirichletCharacter.conductor he
  rw [DirichletCharacter.conductor_changeLevel,DirichletCharacter.conductor_changeLevel,
    hχ,hψ] at hc
  exact hqr hc

lemma productCharacter_toArithmeticFunction {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) :
    toArithmeticFunction (productCharacter χ ψ ·)=
      (toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·)) := by
  ext n
  by_cases hn : n=0
  · simp [hn]
  · rw [ArithmeticFunction.pmul_apply]
    simp [toArithmeticFunction,hn,productCharacter_apply]

end

section

open Complex Filter Topology Set MeasureTheory Finset

open scoped ComplexOrder in
lemma zeta_product_residue_lower {P : ℂ → ℂ} {a : ℕ → ℂ} {A B Q β ε : ℝ}
    (hP : DifferentiableOn ℂ P {s : ℂ | 0 < s.re})
    (hB : 0≤B) (hb : ∀ s ∈ Metric.closedBall (2:ℂ) (7/4:ℝ), ‖P s‖≤B)
    (hA : 0≤A) (hQ : 2≤Q) (hQA : 12*A≤Q) (hBQ : 21*B≤A*Q^4)
    (hβ : 3/4≤β) (hβ1 : β<1) (hβε : 60*(1-β)≤ε)
    (ha : ∀ n, 0≤a n) (ha1 : 1≤a 1) (haC : LSeries.abscissaOfAbsConv a≤1)
    (haP : ∀ s : ℂ, 1 < s.re → LSeries a s=riemannZeta s*P s)
    (hvalue : (riemannZeta β*P β).re≤0) (hreal : (P 1).im=0) :
    ((1-β)/(2*(2-β)))*Q^(-ε)≤(P 1).re := by
  let H := regularizedZetaProduct P
  have hR : P 1=((P 1).re:ℂ) := by apply Complex.ext <;> simp [hreal]
  obtain ⟨hf,hbound⟩ := regularizedZetaProduct_bound hP hB hb
  have he : H =ᶠ[𝓝 (2:ℂ)] fun s => LSeries a s-((P 1).re:ℂ)/(s-1) := by
    filter_upwards [(continuous_re.tendsto (2:ℂ)).eventually
      (lt_mem_nhds (by norm_num : (1:ℝ)<(2:ℂ).re))] with s hs
    have hs1 : s≠1 := by intro h; simp [h] at hs
    rw [show H s=regularizedZetaProduct P s from rfl,regularizedZetaProduct_eq (by linarith) hs1,
      ←haP s hs,hR]
    simp only [Complex.ofReal_re]
  have hac : LSeries.abscissaOfAbsConv a<(2:ℝ) := haC.trans_lt (by exact_mod_cast (show (1:ℝ)<2 by norm_num))
  obtain ⟨ha0,han⟩ := signedTaylorCoeff_regular_nonneg ha ha1 hac he
  have hz : 1<2-β := by linarith
  have hz0 : 0<2-β := by linarith
  have hzr : 2-β<(3/2:ℝ) := by linarith
  have hv : (∑' n : ℕ, signedTaylorCoeff H n*(2-β)^n)≤(P 1).re/((2-β)-1) := by
    rw [(signedTaylorCoeff_hasSum hf.differentiableOn (by rwa [abs_of_pos hz0])).tsum_eq]
    have hβ0 : 0<β := by linarith
    have hβne : (β:ℂ)≠1 := by intro h; have := congrArg Complex.re h; simp at this <;> linarith
    rw [show (2-(2-β):ℝ)=β by ring]
    change (regularizedZetaProduct P β).re≤_
    rw [regularizedZetaProduct_eq hβ0 hβne,Complex.sub_re,hR,
      ←Complex.ofReal_one,←Complex.ofReal_sub,←Complex.ofReal_div,Complex.ofReal_re]
    have hid : (P 1).re/(β-1) = -(P 1).re/((2-β)-1) := by
      rw [show β-1 = -((2-β)-1) by ring,div_neg,neg_div]
    simp only [Complex.ofReal_one,Complex.ofReal_re]
    rw [hid,neg_div,sub_neg_eq_add]
    exact add_le_of_nonpos_left hvalue
  have hn (n : ℕ) : |signedTaylorCoeff H n|≤(A*Q^4)/(3/2)^n := by
    apply (signedTaylorCoeff_norm_bound (by norm_num : (0:ℝ)<3/2) hf
      (fun s hs => (hbound s (Metric.sphere_subset_closedBall hs)).trans hBQ) n)
  have hr := residue_polynomial_lower (ε:=ε) hA hQ hQA hz (by linarith) (by linarith) hn
    (by simpa [signedTaylorCoeff] using ha0) han hv
  convert hr using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  ring

lemma zeta_re_neg_near_one {β : ℝ} (hβ : 99/100≤β) (hβ1 : β<1) :
    (riemannZeta β).re<0 := by
  have hβ0 : 0<β := by linarith
  have hβne : (β:ℂ)≠1 := by intro h; have := congrArg Complex.re h; simp at this <;> linarith
  have hmem : (β:ℂ) ∈ Metric.closedBall 2 (7/4:ℝ) := by
    rw [Metric.mem_closedBall,dist_eq_norm,←Complex.ofReal_ofNat,←Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs,abs_of_neg (by linarith : β-2<0)]
    linarith
  have hb := (Complex.re_le_norm (zetaRegular β)).trans (zetaRegular_norm_le_seventeen hmem)
  rw [zetaRegular_eq hβ0 hβne,Complex.sub_re,←Complex.ofReal_one,
    ←Complex.ofReal_sub,←Complex.ofReal_div,Complex.ofReal_re] at hb
  have hd : 1/(β-1)≤-100 := (div_le_iff_of_neg (by linarith : β-1<0)).mpr (by linarith)
  linarith

end

open Complex Filter Topology Set MeasureTheory Finset ArithmeticFunction

lemma LSeries_zeta_complex_summable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s := by
  apply LSeriesSummable_of_bounded_of_one_lt_re (m:=1) _ hs
  intro n hn
  simp [hn]

lemma biquadraticCoefficients_summable {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (biquadraticCoefficients χ ψ) s := by
  rw [biquadraticCoefficients,←productCharacter_toArithmeticFunction]
  exact ArithmeticFunction.LSeriesSummable_mul
    (ArithmeticFunction.LSeriesSummable_mul
      (ArithmeticFunction.LSeriesSummable_mul (LSeries_zeta_complex_summable hs) (LSeries_character_summable χ hs))
      (LSeries_character_summable ψ hs)) (LSeries_character_summable (productCharacter χ ψ) hs)

lemma LSeries_biquadratic_eq {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) {s : ℂ} (hs : 1 < s.re) :
    LSeries (biquadraticCoefficients χ ψ) s=
      riemannZeta s*(χ.LFunction s*ψ.LFunction s*(productCharacter χ ψ).LFunction s) := by
  have hz := LSeries_zeta_complex_summable hs
  have hχ := LSeries_character_summable χ hs
  have hψ := LSeries_character_summable ψ hs
  have hp := LSeries_character_summable (productCharacter χ ψ) hs
  rw [biquadraticCoefficients,←productCharacter_toArithmeticFunction,
    ArithmeticFunction.LSeries_mul' (ArithmeticFunction.LSeriesSummable_mul (ArithmeticFunction.LSeriesSummable_mul hz hχ) hψ) hp,
    ArithmeticFunction.LSeries_mul' (ArithmeticFunction.LSeriesSummable_mul hz hχ) hψ,
    ArithmeticFunction.LSeries_mul' hz hχ,LSeries_zeta_complex_eq hs,
    LSeries_character_eq χ hs,LSeries_character_eq ψ hs,
    LSeries_character_eq (productCharacter χ ψ) hs]
  ring

lemma quadratic_residue_lower_of_no_root {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ≠1) (hχ2 : χ^2=1)
    {β ε : ℝ} (hβ : 99/100≤β) (hβ1 : β<1) (hβε : 60*(1-β)≤ε)
    (hq : (4032:ℝ)≤q+1) (hz : ∀ x ∈ Set.Icc β 1, χ.LFunction x≠0) :
    ((1-β)/(2*(2-β)))*((q:ℝ)+1)^(-ε)≤‖χ.LFunction 1‖ := by
  have hQ : (2:ℝ)≤q+1 := by linarith
  have hpow : (q:ℝ)+1≤((q:ℝ)+1)^4 := le_self_pow₀ (by linarith) (by norm_num)
  have hv : (riemannZeta β*χ.LFunction β).re≤0 := by
    rw [Complex.mul_re,quadratic_LFunction_im hχ hχ2 (by linarith),mul_zero,sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (zeta_re_neg_near_one hβ hβ1).le
      (quadratic_LFunction_re_pos_of_no_root hχ hχ2 (by linarith) hβ1.le hz).le
  apply le_trans _ (Complex.re_le_norm _)
  apply zeta_product_residue_lower (a:=χ.zetaMul) (A:=336) (B:=16*((q:ℝ)+1))
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn (by positivity)
    (fun s hs => LFunction_norm_polynomial hχ hs) (by norm_num) hQ
    (by norm_num; exact hq) (by nlinarith) (by linarith) hβ1 hβε
    (DirichletCharacter.zetaMul_nonneg hχ2)
    (by simp only [χ.isMultiplicative_zetaMul.map_one,le_refl])
    (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (fun s hs => χ.LSeriesSummable_zetaMul hs))
    (fun s hs => LSeries_zetaMul_eq χ hs) hv
    (by simpa using quadratic_LFunction_im hχ hχ2 (x:=1) zero_lt_one)

lemma biquadratic_norm_bound {q r : ℕ} [NeZero q] [NeZero r]
    {χ : DirichletCharacter ℂ q} {ψ : DirichletCharacter ℂ r}
    (hχ : χ≠1) (hψ : ψ≠1) (hp : productCharacter χ ψ≠1)
    {s : ℂ} (hs : s ∈ Metric.closedBall 2 (7/4:ℝ)) :
    ‖χ.LFunction s*ψ.LFunction s*(productCharacter χ ψ).LFunction s‖≤
      16^3*((q:ℝ)+1)^2*((r:ℝ)+1)^2 := by
  have hq0 : (0:ℝ)≤q := Nat.cast_nonneg q
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
  have hp' := LFunction_norm_polynomial hp hs
  simp only [Nat.cast_mul] at hp'
  calc
    _ ≤ (16*((q:ℝ)+1))*(16*((r:ℝ)+1))*(16*((q:ℝ)*r+1)) := by
      simp only [norm_mul]
      gcongr
      · exact LFunction_norm_polynomial hχ hs
      · exact LFunction_norm_polynomial hψ hs
    _ ≤ _ := by nlinarith [mul_nonneg hq0 hr0]

lemma biquadratic_residue_lower_of_root {q r : ℕ} [NeZero q] [NeZero r]
    {χ : DirichletCharacter ℂ q} {ψ : DirichletCharacter ℂ r}
    (hχ : χ≠1) (hχ2 : χ^2=1) (hψ : ψ≠1) (hψ2 : ψ^2=1)
    (hp : productCharacter ψ χ≠1) {β ε : ℝ}
    (hβ : 3/4≤β) (hβ1 : β<1) (hβε : 60*(1-β)≤ε)
    (hq : (12*(21*16^3*((r:ℝ)+1)^2))≤q+1) (hq1 : (2:ℝ)≤q+1)
    (hz : ψ.LFunction β=0) :
    ((1-β)/(2*(2-β)))*((q:ℝ)+1)^(-ε)≤
      ‖ψ.LFunction 1‖*‖χ.LFunction 1‖*‖(productCharacter ψ χ).LFunction 1‖ := by
  let P := fun s => ψ.LFunction s*χ.LFunction s*(productCharacter ψ χ).LFunction s
  have hd : Differentiable ℂ P :=
    ((DirichletCharacter.differentiable_LFunction hψ).mul
      (DirichletCharacter.differentiable_LFunction hχ)).mul
      (DirichletCharacter.differentiable_LFunction hp)
  have hpow : ((q:ℝ)+1)^2≤((q:ℝ)+1)^4 :=
    pow_le_pow_right₀ (by linarith) (by norm_num)
  have hb : ∀ s ∈ Metric.closedBall (2:ℂ) (7/4:ℝ),
      ‖P s‖≤16^3*((r:ℝ)+1)^2*((q:ℝ)+1)^2 := fun s hs => biquadratic_norm_bound hψ hχ hp hs
  have hiψ : (ψ.LFunction 1).im=0 := by simpa using quadratic_LFunction_im hψ hψ2 (x:=1) zero_lt_one
  have hiχ : (χ.LFunction 1).im=0 := by simpa using quadratic_LFunction_im hχ hχ2 (x:=1) zero_lt_one
  have hip : ((productCharacter ψ χ).LFunction 1).im=0 := by
    simpa using quadratic_LFunction_im hp (productCharacter_quadratic hψ2 hχ2) (x:=1) zero_lt_one
  have hreal : (P 1).im=0 := by simp [P,Complex.mul_im,hiψ,hiχ,hip]
  have hR := zeta_product_residue_lower (P:=P) (a:=biquadraticCoefficients ψ χ)
    (A:=21*16^3*((r:ℝ)+1)^2) (B:=16^3*((r:ℝ)+1)^2*((q:ℝ)+1)^2)
    hd.differentiableOn (by positivity) hb (by positivity) hq1 hq
    (by nlinarith [mul_le_mul_of_nonneg_left hpow (by positivity : (0:ℝ)≤21*16^3*((r:ℝ)+1)^2)])
    hβ hβ1 hβε (biquadraticCoefficients_nonneg hψ2 hχ2)
    (by simp only [(biquadraticCoefficients_multiplicative ψ χ).map_one,le_refl])
    (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun s hs => biquadraticCoefficients_summable ψ χ hs))
    (fun s hs => LSeries_biquadratic_eq ψ χ hs) (by simp [P,hz]) hreal
  have := hR.trans (Complex.re_le_norm (P 1))
  simpa only [P,norm_mul] using this

lemma quadratic_siegel_eventual {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1) :
    ∃ c Q₀ : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ≠1 → χ^2=1 → Q₀≤(q:ℝ)+1 → c*((q:ℝ)+1)^(-ε)≤‖χ.LFunction 1‖ := by
  classical
  let β₀ : ℝ := 1-ε/240
  have hβ₀ : 99/100≤β₀ := by dsimp [β₀] <;> linarith
  have hβ₀1 : β₀<1 := by dsimp [β₀] <;> linarith
  by_cases hex : ∃ r : ℕ, ∃ ψ : DirichletCharacter ℂ (r+1),
      ψ.IsPrimitive ∧ ψ≠1 ∧ ψ^2=1 ∧ ∃ β ∈ Set.Icc β₀ 1, ψ.LFunction β=0
  · obtain ⟨r,ψ,hψprim,hψ,hψ2,β,hβI,hzero⟩ := hex
    have hβ1 : β<1 := lt_of_le_of_ne hβI.2 (by
      intro he
      apply DirichletCharacter.LFunction_apply_one_ne_zero hψ
      simpa [he] using hzero)
    have hβ : 99/100≤β := hβ₀.trans hβI.1
    have hβε : 60*(1-β)≤ε/2 := by dsimp [β₀] at hβI <;> linarith [hβI.1]
    obtain ⟨K,hK,hgrowth⟩ := LFunction_norm_small_power (by linarith : 0<ε/4)
      (by linarith : ε/4≤1/2)
    let D : ℝ := 3*((r:ℝ)+3)
    let U : ℝ := ‖ψ.LFunction 1‖*K*D^(ε/2)
    have hD : 0<D := by dsimp [D] <;> positivity
    have hU : 0<U := by
      exact mul_pos (mul_pos (norm_pos_iff.mpr (DirichletCharacter.LFunction_apply_one_ne_zero hψ)) hK)
        (Real.rpow_pos_of_pos hD _)
    let c : ℝ := (1-β)/(2*(2-β))/U
    have hc : 0 < c := div_pos (div_pos (by linarith) (by linarith)) hU
    refine ⟨c,max (12*(21*16^3*(((r+1:ℕ):ℝ)+1)^2)) ((r:ℝ)+3),hc,?_⟩
    intro q _ χ hχprim hχ hχ2 hq
    have hq1 : (2:ℝ)≤q+1 := by have := (le_max_right _ _).trans hq; have : (0:ℝ) ≤ r := Nat.cast_nonneg r; linarith
    have hqr : r+1≠q := by
      have hr := (le_max_right _ _).trans hq
      intro he
      rw [←he] at hr
      push_cast at hr
      linarith
    have hp : productCharacter ψ χ≠1 :=
      productCharacter_ne_one_of_levels_ne hψprim hχprim hχ2 hqr
    have hl := biquadratic_residue_lower_of_root hχ hχ2 hψ hψ2 hp
      (by linarith) hβ1 hβε ((le_max_left _ _).trans hq) hq1 hzero
    have hb := hgrowth ((r+1)*q) (productCharacter ψ χ) hp 1 (by simp <;> linarith)
    have hQ0 : 0<(q:ℝ)+1 := by positivity
    have he : 2*(ε/4)=ε/2 := by ring
    rw [he] at hb
    have hbase : (((r+1)*q:ℕ):ℝ)+2≤((r:ℝ)+3)*((q:ℝ)+1) := by push_cast <;> nlinarith [Nat.cast_nonneg (α:=ℝ) q,Nat.cast_nonneg (α:=ℝ) r]
    have hb' : ‖(productCharacter ψ χ).LFunction 1‖≤K*D^(ε/2)*((q:ℝ)+1)^(ε/2) := by
      apply hb.trans
      simp only [norm_one]
      calc
        K*(((((r+1)*q:ℕ):ℝ)+2)*(1+2))^(ε/2) ≤ K*(D*((q:ℝ)+1))^(ε/2) := by
          apply mul_le_mul_of_nonneg_left _ hK.le
          apply Real.rpow_le_rpow (by positivity) _ (by linarith)
          dsimp [D]
          nlinarith
        _ = _ := by rw [Real.mul_rpow hD.le hQ0.le]; ring
    have hupper : ‖ψ.LFunction 1‖*‖χ.LFunction 1‖*‖(productCharacter ψ χ).LFunction 1‖≤
        U*((q:ℝ)+1)^(ε/2)*‖χ.LFunction 1‖ := by
      calc
        _ ≤ ‖ψ.LFunction 1‖*‖χ.LFunction 1‖*(K*D^(ε/2)*((q:ℝ)+1)^(ε/2)) := by gcongr
        _ = _ := by dsimp [U] <;> ring
    have hlow := hl.trans hupper
    have hQp : 0<((q:ℝ)+1)^(ε/2) := Real.rpow_pos_of_pos hQ0 _
    have hexp : ((q:ℝ)+1)^(-ε)*((q:ℝ)+1)^(ε/2)=((q:ℝ)+1)^(-(ε/2)) := by
      rw [←Real.rpow_add hQ0]; congr 1; ring
    have hfinal : U*(c*((q:ℝ)+1)^(-ε)*((q:ℝ)+1)^(ε/2)) ≤
        U*(‖χ.LFunction 1‖*((q:ℝ)+1)^(ε/2)) := by
      calc
        U*(c*((q:ℝ)+1)^(-ε)*((q:ℝ)+1)^(ε/2)) =
            ((1-β)/(2*(2-β)))*((q:ℝ)+1)^(-(ε/2)) := by
          rw [mul_assoc c,hexp]
          dsimp [c]
          field_simp
        _ ≤ U*(‖χ.LFunction 1‖*((q:ℝ)+1)^(ε/2)) := by simpa only [mul_assoc,mul_left_comm,mul_comm] using hlow
    exact (mul_le_mul_iff_left₀ hQp).mp ((mul_le_mul_iff_right₀ hU).mp hfinal)
  · refine ⟨(1-β₀)/(2*(2-β₀)),4032,div_pos (by linarith) (by linarith),?_⟩
    intro q hq χ hχprim hχ hχ2 hqbig
    apply quadratic_residue_lower_of_no_root hχ hχ2 hβ₀ hβ₀1
      (by dsimp [β₀] <;> linarith) hqbig
    intro x hx hz
    apply hex
    cases q with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ q => exact ⟨q,χ,hχprim,hχ,hχ2,x,hx,hz⟩

lemma finite_positive_lower {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i∈S,0<f i) : ∃ c : ℝ, 0 < c ∧ ∀ i∈S,c≤f i := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1,zero_lt_one,by simp⟩
  | @insert a S ha ih =>
    obtain ⟨c,hc,hcb⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    refine ⟨min c (f a),lt_min hc (hf a (Finset.mem_insert_self _ _)),?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl|hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hcb i hi)

lemma LFunction_one_finite_lower (N : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      q≤N → χ≠1 → c≤‖χ.LFunction 1‖ := by
  classical
  induction N with
  | zero => exact ⟨1,zero_lt_one,fun q _ χ hq _ => (NeZero.ne q (Nat.eq_zero_of_le_zero hq)).elim⟩
  | succ N ih =>
    obtain ⟨c,hc,hcb⟩ := ih
    obtain ⟨d,hd,hdb⟩ := finite_positive_lower
      ((Finset.univ : Finset (DirichletCharacter ℂ (N+1))).filter (·≠1))
      (fun χ => ‖χ.LFunction 1‖) (fun χ hχ =>
        norm_pos_iff.mpr (DirichletCharacter.LFunction_apply_one_ne_zero (Finset.mem_filter.mp hχ).2))
    refine ⟨min c d,lt_min hc hd,?_⟩
    intro q _ χ hq hχ
    rcases Nat.le_succ_iff_eq_or_le.mp hq with rfl|hq
    · exact (min_le_right _ _).trans (hdb χ (by simp [hχ]))
    · exact (min_le_left _ _).trans (hcb q χ hq hχ)

theorem quadratic_siegel {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ≠1 → χ^2=1 → c*((q:ℝ)+1)^(-ε)≤‖χ.LFunction 1‖ := by
  obtain ⟨c,Q₀,hc,hcb⟩ := quadratic_siegel_eventual hε hε1
  obtain ⟨d,hd,hdb⟩ := LFunction_one_finite_lower ⌈Q₀⌉₊
  refine ⟨min c d,lt_min hc hd,?_⟩
  intro q _ χ hχp hχ hχ2
  by_cases hq : Q₀≤(q:ℝ)+1
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg (by positivity) _)).trans
      (hcb q χ hχp hχ hχ2 hq)
  · have hqn : q≤⌈Q₀⌉₊ := by
      have := Nat.le_ceil Q₀
      have : (q:ℝ)≤(⌈Q₀⌉₊:ℝ) := by linarith
      exact_mod_cast this
    have hp : ((q:ℝ)+1)^(-ε)≤1 := Real.rpow_le_one_of_one_le_of_nonpos (by have := Nat.cast_nonneg (α:=ℝ) q; linarith) (by linarith)
    exact (mul_le_of_le_one_right (le_of_lt (lt_min hc hd)) hp).trans
      ((min_le_right _ _).trans (hdb q χ hqn hχ))

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIQ083_JD.PrimeGaps_ZeroFreeBounds
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

section

open Complex Filter Topology Set MeasureTheory Finset

lemma periodic_sum_norm_le_mul {f : ℕ → ℂ} {q : ℕ} {D : ℝ} (hq : 0<q) (hD : 0≤D)
    (hp : ∀ n,f (q+n)=f n) (hz : ∑ n∈range q,f n=0)
    (hb : ∀ n,‖f n‖≤D) (N : ℕ) : ‖∑ n∈range N,f n‖≤q*D := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases hN : N<q
    · calc
        _ ≤ ∑ n∈range N,‖f n‖ := norm_sum_le _ _
        _ ≤ ∑ _n∈range N,D := sum_le_sum (fun n _ => hb n)
        _ = N*D := by simp
        _ ≤ q*D := mul_le_mul_of_nonneg_right (by exact_mod_cast hN.le) hD
    · have he : q+(N-q)=N := Nat.add_sub_of_le (not_lt.mp hN)
      rw [←he,sum_range_add,hz,zero_add]
      simp_rw [hp]
      exact ih _ (Nat.sub_lt (lt_of_lt_of_le hq (not_lt.mp hN)) hq)

lemma characterMean_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖characterMean χ‖≤1 := by
  rw [characterMean,norm_div,Complex.norm_natCast]
  apply (div_le_one (by exact_mod_cast NeZero.pos q : (0:ℝ)<q)).mpr
  calc
    _ ≤ ∑ n∈range q,‖χ (n : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _n∈range q,(1:ℝ) := sum_le_sum (fun n _ => χ.norm_le_one _)
    _ = q := by simp

lemma characterMean_eq_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ≠1) :
    characterMean χ=0 := by simp [characterMean,char_sum_range_zero hχ]

lemma discrepancy_characterMean_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {t : ℝ} (ht : 1≤t) :
    ‖seriesDiscrepancy (positiveCoefficients (fun n => χ (n : ZMod q))) (characterMean χ) t‖≤2*q+3 := by
  let c := characterMean χ
  have hc : ‖c‖≤1 := characterMean_norm_le χ
  have hb (n : ℕ) : ‖χ (n : ZMod q)-c‖≤2 := (norm_sub_le _ _).trans (by linarith [χ.norm_le_one (n : ZMod q)])
  have hz : ∑ n∈range q,(χ (n : ZMod q)-c)=0 := by
    rw [sum_sub_distrib,sum_const,card_range,nsmul_eq_mul]
    dsimp [c,characterMean]
    have hq : (q:ℂ)≠0 := by exact_mod_cast NeZero.ne q
    field_simp
    ring
  have hr := periodic_sum_norm_le_mul (NeZero.pos q) (by norm_num : (0:ℝ)≤2)
    (f:=fun n => χ (n : ZMod q)-c) (by intro n; simp) hz hb (⌊t⌋₊+1)
  have he : ∑ n∈range (⌊t⌋₊+1),(χ (n : ZMod q)-c) =
      χ (0 : ZMod q)-c+ ∑ n∈Icc 1 ⌊t⌋₊,(χ (n : ZMod q)-c) := by
    rw [Nat.range_succ_eq_Icc_zero,←Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le ⌊t⌋₊)]
    simp
    ring
  have ht0 : 0≤t := by linarith
  have hfloor : ‖(⌊t⌋₊:ℂ)-(t:ℂ)‖≤1 := by
    rw [←Complex.ofReal_natCast,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr (Nat.floor_le ht0))]
    have := Nat.lt_floor_add_one t
    linarith
  have heq : seriesDiscrepancy (positiveCoefficients (fun n => χ (n : ZMod q))) c t =
      (∑ n∈range (⌊t⌋₊+1),(χ (n : ZMod q)-c))-(χ 0-c)+c*((⌊t⌋₊:ℂ)-(t:ℂ)) := by
    rw [he]
    simp only [seriesDiscrepancy,sum_positiveCoefficients,sum_sub_distrib,sum_const,Nat.card_Icc,
      Nat.add_sub_cancel,nsmul_eq_mul]
    ring
  rw [heq]
  calc
    _ ≤ ‖∑ n∈range (⌊t⌋₊+1),(χ (n : ZMod q)-c)‖+‖χ 0-c‖+‖c*((⌊t⌋₊:ℂ)-(t:ℂ))‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (q:ℝ)*2+2+1 := by
      gcongr
      · simpa using hb 0
      · rw [norm_mul]; exact (mul_le_mul hc hfloor (norm_nonneg _) zero_le_one).trans_eq (by ring)
    _ = _ := by ring

lemma LFunction_regularSeries_characterMean {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    χ.LFunction s = regularSeries (positiveCoefficients (fun n => χ (n : ZMod q))) (characterMean χ) s+
      characterMean χ/(s-1) := by
  rw [regularSeries_eq_LSeries_sub (positiveCoefficients_norm_le (fun n => χ.norm_le_one _))
    (by positivity : (0:ℝ)≤2*q+3) (fun t ht => discrepancy_characterMean_bound χ ht.le) hs,
    sub_add_cancel,LSeries_positiveCoefficients,←χ.LFunction_eq_LSeries hs]

lemma LFunction_deriv_norm_small_power {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1/2) :
    ∃ K : ℝ,0<K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),χ≠1 →
      ∀ s : ℂ,1-ε/2 ≤ s.re → ‖deriv χ.LFunction s‖≤K*((q+2)*(‖s‖+2))^(2*ε) := by
  obtain ⟨K,hK,h⟩ := regularSeries_deriv_norm_small_power hε hε1
  refine ⟨K,hK,?_⟩
  intro q _ χ hχ s hs
  have he : regularSeries (positiveCoefficients (fun n => χ (n : ZMod q))) 0 =ᶠ[𝓝 s] χ.LFunction := by
    filter_upwards [(continuous_re.tendsto s).eventually (lt_mem_nhds (by linarith : 0 < s.re))] with z hz
    exact regularSeries_character_eq hχ hz
  rw [←he.deriv_eq]
  have hb := h _ 0 (q+1) (positiveCoefficients_zero _) (positiveCoefficients_norm_le (fun n => χ.norm_le_one _))
    (by simp) (by positivity) (fun t _ => discrepancy_character_bound hχ t) s hs
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  congr 3
  ring

lemma character_line_bounds {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1/2) :
    ∃ K : ℝ,1≤K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ),
      (∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
        ‖characterRegular χ s‖≤K*((q+2)*(|t|+2))^(2*ε)) ∧
      (χ≠1 → ∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
        ‖deriv χ.LFunction s‖≤K*((q+2)*(|t|+2))^(2*ε)) := by
  obtain ⟨K₀,hK₀,h₀⟩ := regularSeries_norm_small_power hε hε1
  obtain ⟨K₁,hK₁,h₁⟩ := LFunction_deriv_norm_small_power hε hε1
  let K := 1+K₀*8^(2*ε)+K₁*4^(2*ε)
  have hp₀ : 0≤K₀*8^(2*ε) := by positivity
  have hp₁ : 0≤K₁*4^(2*ε) := by positivity
  have hK : 1≤K := by dsimp [K] <;> linarith
  refine ⟨K,hK,?_⟩
  intro q _ χ t
  have hq : (0:ℝ)≤q := Nat.cast_nonneg q
  have ht : 0≤|t| := abs_nonneg t
  have hp : 0≤((q:ℝ)+2)*(|t|+2) := by positivity
  have he : 0≤2*ε := by positivity
  constructor
  · intro s hs hn
    have hb := h₀ _ (characterMean χ) (2*q+3) (positiveCoefficients_zero _)
      (positiveCoefficients_norm_le (fun n => χ.norm_le_one _)) (characterMean_norm_le χ)
      (by positivity) (fun t ht => discrepancy_characterMean_bound χ ht) s (by linarith)
    change ‖characterRegular χ s‖≤_ at hb
    have hb' : (2*q+3+1)*(‖s‖+2)≤8*(((q:ℝ)+2)*(|t|+2)) := by
      nlinarith [mul_nonneg (show (0:ℝ)≤2*q+4 by positivity) (sub_nonneg.mpr hn)]
    calc
      _ ≤ K₀*((2*q+3+1)*(‖s‖+2))^(2*ε) := hb
      _ ≤ K₀*(8*(((q:ℝ)+2)*(|t|+2)))^(2*ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hb' he) hK₀.le
      _ = (K₀*8^(2*ε))*(((q:ℝ)+2)*(|t|+2))^(2*ε) := by rw [Real.mul_rpow (by norm_num) hp]; ring
      _ ≤ _ := by gcongr; dsimp [K] <;> linarith
  · intro hχ s hs hn
    have hb := h₁ q χ hχ s (by linarith)
    have hb' : (q+2)*(‖s‖+2)≤4*(((q:ℝ)+2)*(|t|+2)) := by
      nlinarith [mul_nonneg (show (0:ℝ)≤q+2 by positivity) (sub_nonneg.mpr hn)]
    calc
      _ ≤ K₁*((q+2)*(‖s‖+2))^(2*ε) := hb
      _ ≤ K₁*(4*(((q:ℝ)+2)*(|t|+2)))^(2*ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hb' he) hK₁.le
      _ = (K₁*4^(2*ε))*(((q:ℝ)+2)*(|t|+2))^(2*ε) := by rw [Real.mul_rpow (by norm_num) hp]; ring
      _ ≤ _ := by gcongr; dsimp [K] <;> linarith

lemma line_growth_lipschitz {f : ℂ → ℂ} {t D : ℝ} (hf : Differentiable ℂ f)
    (hb : ∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) → ‖deriv f s‖≤D)
    {z w : ℂ} (hz : 1 ≤ z.re) (hw : 1 ≤ w.re)
    (hzn : ‖z‖+2≤4*(|t|+2)) (hwn : ‖w‖+2≤4*(|t|+2)) :
    ‖f z-f w‖≤D*‖z-w‖ := by
  let S := {s : ℂ | 1 ≤ s.re} ∩ Metric.closedBall 0 (4*(|t|+2)-2)
  have hS : Convex ℝ S := (convex_halfSpace_re_ge 1).inter (convex_closedBall 0 _)
  apply Convex.norm_image_sub_le_of_norm_deriv_le (s:=S) (fun z _ => hf z) ?_ hS
      ⟨hw,by simp [Metric.mem_closedBall,dist_zero_right] <;> linarith⟩
      ⟨hz,by simp [Metric.mem_closedBall,dist_zero_right] <;> linarith⟩
  intro s hs
  exact hb s hs.1 (by have := hs.2; simp only [Metric.mem_closedBall,dist_zero_right] at this <;> linarith)

end

lemma three_four_one_lower {a D E : ℝ} (ha : 0≤a) (hD : 1≤D) (hE : 1≤E)
    (h : ∀ δ : ℝ,0<δ → δ≤1 → 1≤(2*D/δ)^3*(a+D*δ)^4*E) :
    1/(256*D^6*E)≤a := by
  have hD0 : 0<D := by linarith
  have hE0 : 0<E := by linarith
  let δ := 1/(256*D^7*E)
  have hδ : 0<δ := by dsimp [δ] <;> positivity
  have hδ1 : δ≤1 := by
    have hp : (1:ℝ)≤D^7 := one_le_pow₀ hD
    have hp' : (1:ℝ)≤D^7*E := one_le_mul_of_one_le_of_one_le hp hE
    dsimp [δ]
    apply (div_le_one (by positivity)).mpr
    linarith
  have he : 1/(256*D^6*E)=D*δ := by dsimp [δ]; field_simp
  rw [he]
  by_contra! han
  have hb : a+D*δ≤2*D*δ := by linarith
  have hh := h δ hδ hδ1
  have hu : (2*D/δ)^3*(a+D*δ)^4*E≤(2*D/δ)^3*(2*D*δ)^4*E := by gcongr
  have hv : (2*D/δ)^3*(2*D*δ)^4*E=1/2 := by dsimp [δ]; field_simp <;> norm_num
  rw [hv] at hu
  linarith

open Complex Filter Topology Finset

lemma line_sample_norm {δ t u : ℝ} (hδ : 0≤δ) (hδ1 : δ≤1) (hu : |u|≤2*|t|) :
    ‖(1:ℂ)+δ+I*u‖+2≤4*(|t|+2) := by
  have h := Complex.norm_le_abs_re_add_abs_im ((1:ℂ)+δ+I*u)
  simp only [Complex.add_re,Complex.one_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
    Complex.I_im,Complex.ofReal_im,mul_zero,zero_mul,sub_self,add_zero,Complex.add_im,
    Complex.one_im,Complex.mul_im,one_mul,zero_add] at h
  rw [abs_of_nonneg (by linarith : (0:ℝ)≤1+δ)] at h
  linarith [abs_nonneg t]

lemma LFunction_norm_le_regular_add_pole {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    ‖χ.LFunction s‖≤‖characterRegular χ s‖+1/‖s-1‖ := by
  rw [LFunction_regularSeries_characterMean χ hs]
  apply (norm_add_le _ _).trans
  dsimp [characterRegular]
  apply add_le_add le_rfl
  rw [norm_div]
  exact div_le_div_of_nonneg_right (characterMean_norm_le χ) (norm_nonneg _)

lemma characterRegular_eq_nonprincipal {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) {s : ℂ} (hs : 0 < s.re) : characterRegular χ s=χ.LFunction s := by
  rw [characterRegular,characterMean_eq_zero hχ,regularSeries_character_eq hχ hs]

lemma nonprincipal_line_lower_aux {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) {t c K P : ℝ} (hc : 0 < c) (_hc1 : c≤1) (hK : 1≤K) (hP : 1≤P)
    (hr : ∀ ψ : DirichletCharacter ℂ q,∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
      ‖characterRegular ψ s‖≤K*P)
    (hd : ∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) → ‖deriv χ.LFunction s‖≤K*P)
    (hsi : χ^2=1 → c/P≤‖χ.LFunction 1‖) :
    min (c/2) (1/(256*K^6*(K+K/c)))/P^8≤‖χ.LFunction (1+I*t)‖ := by
  have hK0 : 0<K := by linarith
  have hP0 : 0<P := by linarith
  have hhc : 0<K+K/c := by positivity
  have hKP : 1≤K*P := one_le_mul_of_one_le_of_one_le hK hP
  have hn0 : ‖(1:ℂ)+I*t‖+2≤4*(|t|+2) := by
    simpa using line_sample_norm (t:=t) (u:=t) (δ:=0) le_rfl zero_le_one (by linarith [abs_nonneg t])
  have hn1 : ‖(1:ℂ)‖+2≤4*(|t|+2) := by norm_num; linarith [abs_nonneg t]
  by_cases hsmall : χ^2=1 ∧ |t| ≤ c/(2*K*P^2)
  · have hdiff := line_growth_lipschitz (DirichletCharacter.differentiable_LFunction hχ) hd
      (z:=1) (w:=1+I*t) (by simp) (by simp) hn1 hn0
    have hnorm : ‖(1:ℂ)-(1+I*t)‖=|t| := by
      rw [show (1:ℂ)-(1+I*t)=-(I*t) by ring,norm_neg,norm_mul,Complex.norm_I,one_mul,
        Complex.norm_real,Real.norm_eq_abs]
    rw [hnorm] at hdiff
    have hdiff' : ‖χ.LFunction 1-χ.LFunction (1+I*t)‖ ≤ c/(2*P) := by
      calc
        _ ≤ K*P*|t| := hdiff
        _ ≤ K*P*(c/(2*K*P^2)) := mul_le_mul_of_nonneg_left hsmall.2 (by positivity)
        _ = _ := by field_simp
    have hval : c/(2*P)≤‖χ.LFunction (1+I*t)‖ := by
      have htri := norm_add_le (χ.LFunction 1-χ.LFunction (1+I*t)) (χ.LFunction (1+I*t))
      rw [sub_add_cancel] at htri
      have he : c/P=2*(c/(2*P)) := by ring
      have hsi' := hsi hsmall.1
      rw [he] at hsi'
      linarith
    have hP8 : P≤P^8 := by simpa using pow_le_pow_right₀ hP (show (1:ℕ)≤8 by norm_num)
    calc
      _ ≤ (c/2)/P^8 := div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)
      _ ≤ (c/2)/P := div_le_div_of_nonneg_left (by positivity) hP0 hP8
      _ = c/(2*P) := by ring
      _ ≤ _ := hval
  · have hLo : 1/(256*(K*P)^6*((K+K/c)*P^2))≤‖χ.LFunction (1+I*t)‖ := by
      apply three_four_one_lower (norm_nonneg _) hKP
        (one_le_mul_of_one_le_of_one_le (by linarith [div_pos hK0 hc]) (one_le_pow₀ hP))
      intro δ hδ hδ1
      have hrδ : ((1:ℂ)+δ+I*t).re=1+δ := by simp
      have hrδ2 : ((1:ℂ)+δ+2*I*t).re=1+δ := by simp
      have hnδ := line_sample_norm hδ.le hδ1 (t:=t) (u:=t) (by linarith [abs_nonneg t])
      have hnδ2 : ‖(1:ℂ)+δ+2*I*t‖+2≤4*(|t|+2) := by
        simpa only [show I*((2*t:ℝ):ℂ)=2*I*t by push_cast; ring] using
          line_sample_norm hδ.le hδ1 (t:=t) (u:=2*t) (by rw [abs_mul]; norm_num)
      have hL0 : ‖DirichletCharacter.LFunctionTrivChar q (1+δ)‖≤2*(K*P)/δ := by
        have hn : ‖(1:ℂ)+δ‖+2≤4*(|t|+2) := by
          simpa using line_sample_norm hδ.le hδ1 (t:=t) (u:=0) (by simp)
        have hreg := hr (1:DirichletCharacter ℂ q) (1+δ) (by simp <;> linarith) hn
        have hp := LFunction_norm_le_regular_add_pole (1:DirichletCharacter ℂ q)
          (s:=1+δ) (by simp <;> linarith)
        have hden : ‖(1:ℂ)+δ-1‖=δ := by simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ]
        rw [hden] at hp
        change ‖DirichletCharacter.LFunction (1:DirichletCharacter ℂ q) (1+δ)‖≤_
        apply (hp.trans (add_le_add hreg le_rfl)).trans
        apply (le_div_iff₀ hδ).mpr
        have hd : (K*P)*δ≤K*P := mul_le_of_le_one_right (by positivity) hδ1
        field_simp
        nlinarith
      have hLχ : ‖χ.LFunction (1+δ+I*t)‖≤‖χ.LFunction (1+I*t)‖+(K*P)*δ := by
        have hl := line_growth_lipschitz (DirichletCharacter.differentiable_LFunction hχ) hd
          (z:=1+δ+I*t) (w:=1+I*t) (by simp <;> linarith) (by simp) hnδ hn0
        have hden : ‖(1:ℂ)+δ+I*t-(1+I*t)‖=δ := by
          rw [show (1:ℂ)+δ+I*t-(1+I*t)=(δ:ℂ) by ring,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ]
        rw [hden] at hl
        have ht := norm_add_le (χ.LFunction (1+δ+I*t)-χ.LFunction (1+I*t)) (χ.LFunction (1+I*t))
        rw [sub_add_cancel] at ht
        linarith
      have hL2 : ‖(χ^2).LFunction (1+δ+2*I*t)‖≤(K+K/c)*P^2 := by
        by_cases hχ2 : χ^2=1
        · have ht : c/(2*K*P^2)< |t| := lt_of_not_ge (fun ht => hsmall ⟨hχ2,ht⟩)
          have ht0 : 0< |t| := (by positivity : 0 < c/(2*K*P^2)).trans ht
          have hp := LFunction_norm_le_regular_add_pole (χ^2) (s:=1+δ+2*I*t) (by rw [hrδ2]; linarith)
          have hn : 2*|t|≤‖(1:ℂ)+δ+2*I*t-1‖ := by
            have h := Complex.abs_im_le_norm ((1:ℂ)+δ+2*I*t-1)
            simpa [abs_mul] using h
          have hfrac : 1/‖(1:ℂ)+δ+2*I*t-1‖≤K*P^2/c := by
            apply (div_le_div_of_nonneg_left zero_le_one (by positivity : 0<2*|t|) hn).trans
            apply (div_le_iff₀ (by positivity : 0<2*|t|)).mpr
            have ht' := (div_lt_iff₀ (by positivity : 0<2*K*P^2)).mp ht
            rw [div_mul_eq_mul_div]
            apply (le_div_iff₀ hc).mpr
            nlinarith
          have hreg := hr (χ^2) (1+δ+2*I*t) (by rw [hrδ2]; linarith) hnδ2
          have hP2 : P≤P^2 := by nlinarith
          have h := hp.trans (add_le_add hreg hfrac)
          apply h.trans
          calc
            K*P+K*P^2/c ≤ K*P^2+K*P^2/c := add_le_add (mul_le_mul_of_nonneg_left hP2 hK0.le) le_rfl
            _ = _ := by ring
        · have hreg := hr (χ^2) (1+δ+2*I*t) (by rw [hrδ2]; linarith) hnδ2
          rw [characterRegular_eq_nonprincipal hχ2 (by rw [hrδ2]; linarith)] at hreg
          have hP2 : P≤P^2 := by nlinarith
          exact hreg.trans (by nlinarith [mul_le_mul_of_nonneg_left hP2 hK0.le,div_pos hK0 hc])
      have hprod := χ.norm_LFunction_product_ge_one hδ t
      simp only [norm_mul,norm_pow] at hprod
      exact hprod.trans (by gcongr)
    calc
      _ ≤ (1/(256*K^6*(K+K/c)))/P^8 := div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = 1/(256*(K*P)^6*((K+K/c)*P^2)) := by field_simp
      _ ≤ _ := hLo

lemma nonprincipal_line_lower {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1) :
    ∃ c : ℝ,0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ≠1 → ∀ t : ℝ,
        c*(((q:ℝ)+2)*(|t|+2))^(-ε)≤‖χ.LFunction (1+I*t)‖ := by
  obtain ⟨K,hK,hgrowth⟩ := character_line_bounds (by linarith : 0<ε/16) (by linarith : ε/16≤1/2)
  obtain ⟨c₀,hc₀,hsiegel⟩ := quadratic_siegel (by linarith : 0<ε/8) (by linarith : ε/8≤1)
  let c := min c₀ 1
  have hc : 0 < c := lt_min hc₀ zero_lt_one
  have hc1 : c≤1 := min_le_right _ _
  let d := min (c/2) (1/(256*K^6*(K+K/c)))
  have hK0 : 0<K := by linarith
  have hd : 0<d := by dsimp [d] <;> positivity
  refine ⟨d,hd,?_⟩
  intro q _ χ hχp hχ t
  let X : ℝ := ((q:ℝ)+2)*(|t|+2)
  let P : ℝ := X^(ε/8)
  have hX : 1≤X := by dsimp [X] <;> nlinarith [Nat.cast_nonneg (α:=ℝ) q,abs_nonneg t]
  have hX0 : 0<X := by linarith
  have hP : 1≤P := Real.one_le_rpow hX (by positivity)
  have he : 2*(ε/16)=ε/8 := by ring
  have hsi : χ^2=1 → c/P≤‖χ.LFunction 1‖ := by
    intro hχ2
    have hq : (q:ℝ)+1≤X := by dsimp [X] <;> nlinarith [Nat.cast_nonneg (α:=ℝ) q,abs_nonneg t]
    calc
      c/P = c*X^(-(ε/8)) := by rw [Real.rpow_neg hX0.le]; rfl
      _ ≤ c₀*((q:ℝ)+1)^(-(ε/8)) := by
        apply mul_le_mul (min_le_left _ _) (Real.rpow_le_rpow_of_nonpos (by positivity) hq (by linarith))
          (Real.rpow_nonneg hX0.le _) hc₀.le
      _ ≤ _ := hsiegel q χ hχp hχ hχ2
  have hh := nonprincipal_line_lower_aux hχ hc hc1 hK hP
    (fun ψ s hs hn => by simpa only [he] using (hgrowth q ψ t).1 s hs hn)
    (fun s hs hn => by simpa only [he] using (hgrowth q χ t).2 hχ s hs hn) hsi
  have hP8 : P^8=X^ε := by
    dsimp [P]
    rw [←Real.rpow_mul_natCast hX0.le]
    congr 1
    norm_num
  change d/P^8≤_ at hh
  rw [hP8] at hh
  change d*X^(-ε)≤_
  simpa only [Real.rpow_neg hX0.le,div_eq_mul_inv] using hh

lemma character_interior_lower {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {t K P δ : ℝ} (hK : 1≤K) (hP : 1≤P) (hδ : 0<δ) (hδ1 : δ≤1)
    (hr : ∀ ψ : DirichletCharacter ℂ q,∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
      ‖characterRegular ψ s‖≤K*P) :
    δ/(2*K*P)≤‖χ.LFunction (1+δ+I*t)‖ := by
  have hKP : 1≤K*P := one_le_mul_of_one_le_of_one_le hK hP
  have hKP0 : 0<K*P := by linarith
  have hb (ψ : DirichletCharacter ℂ q) (u : ℝ) (hu : |u|≤2*|t|) :
      ‖ψ.LFunction (1+δ+I*u)‖≤2*K*P/δ := by
    have hp := LFunction_norm_le_regular_add_pole ψ (s:=1+δ+I*u) (by simp <;> linarith)
    have hn : δ≤‖(1:ℂ)+δ+I*u-1‖ := by
      simpa using Complex.re_le_norm ((1:ℂ)+δ+I*u-1)
    have hreg := hr ψ (1+δ+I*u) (by simp <;> linarith) (line_sample_norm hδ.le hδ1 hu)
    have hfrac := div_le_div_of_nonneg_left zero_le_one hδ hn
    apply (hp.trans (add_le_add hreg hfrac)).trans
    apply (le_div_iff₀ hδ).mpr
    have hd := mul_le_of_le_one_right hKP0.le hδ1
    have he : (K*P+1/δ)*δ=K*P*δ+1 := by field_simp
    rw [he]
    nlinarith
  have h0 : ‖DirichletCharacter.LFunctionTrivChar q (1+δ)‖≤2*K*P/δ := by
    simpa using hb (1:DirichletCharacter ℂ q) 0 (by simp)
  have h2 : ‖(χ^2).LFunction (1+δ+2*I*t)‖≤2*K*P/δ := by
    simpa only [show I*((2*t:ℝ):ℂ)=2*I*t by push_cast; ring] using hb (χ^2) (2*t) (by rw [abs_mul]; norm_num)
  have hh := χ.norm_LFunction_product_ge_one hδ t
  simp only [norm_mul,norm_pow] at hh
  have hu : 1≤(2*K*P/δ)^3*‖χ.LFunction (1+δ+I*t)‖^4*(2*K*P/δ) := hh.trans (by gcongr)
  have hp : (1:ℝ)^4≤((2*K*P/δ)*‖χ.LFunction (1+δ+I*t)‖)^4 := by convert hu using 1 <;> first | (with_reducible_and_instances rfl) | ring
  have hv := le_of_pow_le_pow_left₀ (by norm_num : (4:ℕ)≠0) (by positivity) hp
  apply (div_le_iff₀ (by positivity : 0<2*K*P)).mpr
  have he : (2*K*P/δ)*‖χ.LFunction (1+δ+I*t)‖=(‖χ.LFunction (1+δ+I*t)‖*(2*K*P))/δ := by ring
  rw [he] at hv
  simpa only [one_mul] using (le_div_iff₀ hδ).mp hv

lemma nonprincipal_strip_lower_aux {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) {t c K P δ : ℝ} (hc : 0 < c) (hK : 1≤K) (hP : 1≤P)
    (hδ : 0≤δ) (hδ1 : δ≤1)
    (hr : ∀ ψ : DirichletCharacter ℂ q,∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
      ‖characterRegular ψ s‖≤K*P)
    (hd : ∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) → ‖deriv χ.LFunction s‖≤K*P)
    (hl : c/P≤‖χ.LFunction (1+I*t)‖) :
    (c/(4*K^2))/P^3≤‖χ.LFunction (1+δ+I*t)‖ := by
  have hK0 : 0<K := by linarith
  have hP0 : 0<P := by linarith
  by_cases hnear : δ ≤ c/(2*K*P^2)
  · have hn0 : ‖(1:ℂ)+I*t‖+2≤4*(|t|+2) := by
      simpa using line_sample_norm (t:=t) (u:=t) (δ:=0) le_rfl zero_le_one (by linarith [abs_nonneg t])
    have hnδ := line_sample_norm hδ hδ1 (t:=t) (u:=t) (by linarith [abs_nonneg t])
    have hdif := line_growth_lipschitz (DirichletCharacter.differentiable_LFunction hχ) hd
      (z:=1+I*t) (w:=1+δ+I*t) (by simp) (by simp <;> linarith) hn0 hnδ
    have hnorm : ‖(1:ℂ)+I*t-(1+δ+I*t)‖=δ := by
      rw [show (1:ℂ)+I*t-(1+δ+I*t)=-(δ:ℂ) by ring,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hδ]
    rw [hnorm] at hdif
    have hdb : ‖χ.LFunction (1+I*t)-χ.LFunction (1+δ+I*t)‖ ≤ c/(2*P) := by
      apply hdif.trans
      calc
        K*P*δ ≤ K*P*(c/(2*K*P^2)) := mul_le_mul_of_nonneg_left hnear (by positivity)
        _ = _ := by field_simp
    have htri := norm_add_le (χ.LFunction (1+I*t)-χ.LFunction (1+δ+I*t)) (χ.LFunction (1+δ+I*t))
    rw [sub_add_cancel] at htri
    have hva : c/(2*P)≤‖χ.LFunction (1+δ+I*t)‖ := by
      have he : c/P=2*(c/(2*P)) := by ring
      rw [he] at hl
      linarith
    apply le_trans ?_ hva
    rw [div_div]
    apply div_le_div_of_nonneg_left hc.le (by positivity)
    have hP3 : P≤P^3 := by simpa using pow_le_pow_right₀ hP (show (1:ℕ)≤3 by norm_num)
    have hK2 : 1≤K^2 := one_le_pow₀ hK
    nlinarith [mul_le_mul_of_nonneg_left hP3 (show (0:ℝ)≤4*K^2 by positivity)]
  · have hδ0 : 0<δ := (by positivity : 0 < c/(2*K*P^2)).trans (lt_of_not_ge hnear)
    apply le_trans ?_ (character_interior_lower χ hK hP hδ0 hδ1 hr)
    calc
      (c/(4*K^2))/P^3 = (c/(2*K*P^2))/(2*K*P) := by field_simp <;> norm_num
      _ ≤ δ/(2*K*P) := div_le_div_of_nonneg_right (le_of_not_ge hnear) (by positivity)

lemma nonprincipal_strip_lower {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1) :
    ∃ c : ℝ,0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ≠1 → ∀ σ t : ℝ, 1≤σ → σ≤2 →
        c*(((q:ℝ)+2)*(|t|+2))^(-ε)≤‖χ.LFunction (σ+I*t)‖ := by
  obtain ⟨K,hK,hg⟩ := character_line_bounds (by linarith : 0<ε/6) (by linarith : ε/6≤1/2)
  obtain ⟨c,hc,hl⟩ := nonprincipal_line_lower (by linarith : 0<ε/3) (by linarith : ε/3≤1)
  have hK0 : 0<K := by linarith
  refine ⟨c/(4*K^2),by positivity,?_⟩
  intro q _ χ hχp hχ σ t hσ hσ2
  let X : ℝ := ((q:ℝ)+2)*(|t|+2)
  let P : ℝ := X^(ε/3)
  have hX : 1≤X := by dsimp [X] <;> nlinarith [Nat.cast_nonneg (α:=ℝ) q,abs_nonneg t]
  have hX0 : 0<X := by linarith
  have hP : 1≤P := Real.one_le_rpow hX (by positivity)
  have he : 2*(ε/6)=ε/3 := by ring
  have hl' : c/P≤‖χ.LFunction (1+I*t)‖ := by
    have hh := hl q χ hχp hχ t
    change c*X^(-(ε/3))≤_ at hh
    change c/X^(ε/3)≤_
    simpa only [Real.rpow_neg hX0.le,div_eq_mul_inv] using hh
  have hb := nonprincipal_strip_lower_aux hχ hc hK hP (δ:=σ-1) (by linarith) (by linarith)
    (fun ψ s hs hn => by simpa only [he] using (hg q ψ t).1 s hs hn)
    (fun s hs hn => by simpa only [he] using (hg q χ t).2 hχ s hs hn) hl'
  have hP3 : P^3=X^ε := by dsimp [P]; rw [←Real.rpow_mul_natCast hX0.le]; congr 1; norm_num
  rw [hP3] at hb
  have hs : (1:ℂ)+((σ-1:ℝ):ℂ)+I*t=(σ:ℂ)+I*t := by push_cast <;> ring
  rw [hs] at hb
  change (c/(4*K^2))*X^(-ε)≤_
  simpa only [Real.rpow_neg hX0.le,div_eq_mul_inv] using hb

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterZeroFreeStrip
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A small zero-free strip for primitive nonprincipal characters

The width may be an arbitrary fixed negative power of the modulus and height.
This is sufficient when both parameters are bounded by powers of a logarithm.
-/
namespace JointDickman
open Complex Set

private theorem half_plane_lipschitz {f : ℂ → ℂ} {a R D : ℝ}
    (hf : Differentiable ℂ f)
    (hb : ∀ s : ℂ, a ≤ s.re → ‖s‖ ≤ R → ‖deriv f s‖ ≤ D)
    {z w : ℂ} (hz : a ≤ z.re) (hw : a ≤ w.re)
    (hzn : ‖z‖ ≤ R) (hwn : ‖w‖ ≤ R) :
    ‖f z - f w‖ ≤ D * ‖z-w‖ := by
  let S := {s : ℂ | a ≤ s.re} ∩ Metric.closedBall 0 R
  have hS : Convex ℝ S := (convex_halfSpace_re_ge a).inter (convex_closedBall 0 R)
  apply Convex.norm_image_sub_le_of_norm_deriv_le (s := S) (fun z _ => hf z) ?_ hS
    ⟨hw, by simpa only [Metric.mem_closedBall, dist_zero_right] using hwn⟩
    ⟨hz, by simpa only [Metric.mem_closedBall, dist_zero_right] using hzn⟩
  intro s hs
  exact hb s hs.1 (by simpa only [Metric.mem_closedBall, dist_zero_right] using hs.2)

/-- A Siegel-type strip, with an ineffective constant but uniform modulus and height. -/
theorem primitive_character_zero_free_strip {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ A : ℝ, 0 < A ∧ A ≤ 1/4 ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ ≠ 1 → ∀ σ t : ℝ,
          1 - A * (((q:ℝ)+2)*(|t|+2))^(-ε) ≤ σ → σ ≤ 2 →
          A * (((q:ℝ)+2)*(|t|+2))^(-ε) ≤ ‖χ.LFunction (σ + I*t)‖ := by
  obtain ⟨c,hc,hl⟩ := LargePrimeGaps.nonprincipal_strip_lower
    (show 0 < ε/2 by positivity) (show ε/2 ≤ 1 by linarith)
  obtain ⟨K,hK,hd⟩ := LargePrimeGaps.LFunction_deriv_norm_small_power
    (show 0 < ε/4 by positivity) (show ε/4 ≤ 1/2 by linarith)
  let D := K * (4:ℝ)^(ε/2)
  have hD : 0 < D := by dsimp [D] <;> positivity
  let A := min (ε/8) (min (1/4) (min (c/2) (c/(2*D))))
  have hA : 0 < A := by dsimp [A] <;> positivity
  have hAe : A ≤ ε/8 := min_le_left _ _
  have hA4 : A ≤ 1/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hAc : A ≤ c/2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hAD : A ≤ c/(2*D) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨A,hA,hA4,?_⟩
  intro q _ χ hp hn σ t hσ hσ2
  let W : ℝ := ((q:ℝ)+2)*(|t|+2)
  have hW : 1 ≤ W := by dsimp [W] <;> nlinarith [Nat.cast_nonneg (α := ℝ) q, abs_nonneg t]
  have hW0 : 0 < W := lt_of_lt_of_le zero_lt_one hW
  have hpw : 0 < W^(-ε) := Real.rpow_pos_of_pos hW0 _
  have hpw1 : W^(-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW (by linarith)
  have hpw2 : W^(-ε) ≤ W^(-(ε/2)) :=
    Real.rpow_le_rpow_of_exponent_le hW (by linarith)
  have hsmall : A * W^(-ε) ≤ ε/8 :=
    (mul_le_of_le_one_right hA.le hpw1).trans hAe
  have hσ0 : 0 ≤ σ := by change 1-A*W^(-ε) ≤ σ at hσ; linarith
  have hwanted : A*W^(-ε) ≤ (c/2)*W^(-(ε/2)) :=
    mul_le_mul hAc hpw2 hpw.le (by positivity)
  by_cases hσ1 : 1 ≤ σ
  · exact hwanted.trans ((mul_le_mul_of_nonneg_right (by linarith : c/2 ≤ c)
      (Real.rpow_nonneg hW0.le _)).trans (hl q χ hp hn σ t hσ1 hσ2))
  have hσlt : σ < 1 := lt_of_not_ge hσ1
  let w : ℂ := 1 + I*t
  let z : ℂ := σ + I*t
  have hnorm (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
      ‖(u:ℂ)+I*t‖+2 ≤ 4*(|t|+2) := by
    have hh := Complex.norm_le_abs_re_add_abs_im ((u:ℂ)+I*t)
    simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
      Complex.I_im,Complex.ofReal_im,mul_zero,zero_mul,sub_self,add_zero,
      Complex.add_im,Complex.mul_im,one_mul,zero_add] at hh
    rw [abs_of_nonneg hu] at hh
    linarith [abs_nonneg t]
  have hb (s : ℂ) (hs : 1-ε/8 ≤ s.re) (hsn : ‖s‖ ≤ 4*(|t|+2)-2) :
      ‖deriv χ.LFunction s‖ ≤ D*W^(ε/2) := by
    have hbase : ((q:ℝ)+2)*(‖s‖+2) ≤ 4*W := by
      dsimp [W]
      nlinarith [mul_nonneg (show (0:ℝ) ≤ q+2 by positivity)
        (show 0 ≤ 4*(|t|+2)-(‖s‖+2) by linarith)]
    have he := hd q χ hn s (by linarith)
    rw [show 2*(ε/4) = ε/2 by ring] at he
    calc
      _ ≤ K*(((q:ℝ)+2)*(‖s‖+2))^(ε/2) := he
      _ ≤ K*(4*W)^(ε/2) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hbase (by positivity)) hK.le
      _ = D*W^(ε/2) := by rw [Real.mul_rpow (by norm_num) hW0.le]; dsimp [D] <;> ring
  have hzre : 1-ε/8 ≤ z.re := by
    have hh : 1-ε/8 ≤ σ := by
      change 1-A*W^(-ε) ≤ σ at hσ
      linarith
    simpa [z] using hh
  have hwre : 1-ε/8 ≤ w.re := by
    simpa [w] using (show 1-ε/8 ≤ (1:ℝ) by linarith)
  have hzN : ‖z‖ ≤ 4*(|t|+2)-2 := by dsimp [z]; linarith [hnorm σ hσ0 hσlt.le]
  have hwN : ‖w‖ ≤ 4*(|t|+2)-2 := by
    have hh := hnorm 1 zero_le_one le_rfl
    norm_num only [ofReal_one] at hh
    dsimp [w]
    linarith
  have hdiff := half_plane_lipschitz (DirichletCharacter.differentiable_LFunction hn)
    hb hzre hwre hzN hwN
  have hdist : ‖z-w‖ = 1-σ := by
    have he : z-w = ((σ-1:ℝ):ℂ) := by dsimp [z,w]; push_cast <;> ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  rw [hdist] at hdiff
  have hdiff' : ‖χ.LFunction z-χ.LFunction w‖ ≤ (c/2)*W^(-(ε/2)) := by
    calc
      _ ≤ D*W^(ε/2)*(1-σ) := hdiff
      _ ≤ D*W^(ε/2)*(A*W^(-ε)) := mul_le_mul_of_nonneg_left
        (by change 1-A*W^(-ε) ≤ σ at hσ; linarith) (by positivity)
      _ = (D*A)*W^(-(ε/2)) := by
        rw [mul_mul_mul_comm, ←Real.rpow_add hW0]
        congr 2
        ring
      _ ≤ (c/2)*W^(-(ε/2)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hW0.le _)
        have hh := (le_div_iff₀ (by positivity : 0 < 2*D)).mp hAD
        nlinarith
  have hline : c*W^(-(ε/2)) ≤ ‖χ.LFunction w‖ := by
    simpa only [w, ofReal_one] using hl q χ hp hn 1 t le_rfl (by norm_num)
  have htri : ‖χ.LFunction w‖ ≤ ‖χ.LFunction w-χ.LFunction z‖+‖χ.LFunction z‖ := by
    simpa only [sub_add_cancel] using norm_add_le
      (χ.LFunction w-χ.LFunction z) (χ.LFunction z)
  rw [norm_sub_rev] at hdiff'
  have hh : (c/2)*W^(-(ε/2)) ≤ ‖χ.LFunction z‖ := by linarith
  exact hwanted.trans hh

/-- The same strip is zero-free for imprimitive nonprincipal characters. -/
theorem nonprincipal_character_zero_free_strip {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ A : ℝ, 0 < A ∧ A ≤ 1/4 ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ σ t : ℝ,
        1 - A * (((q:ℝ)+2)*(|t|+2))^(-ε) ≤ σ → σ ≤ 2 →
        χ.LFunction (σ + I*t) ≠ 0 := by
  obtain ⟨A,hA,hA4,h⟩ := primitive_character_zero_free_strip hε hε1
  refine ⟨A,hA,hA4,?_⟩
  intro q _ χ hn σ t hσ hσ2
  let ψ := χ.primitiveCharacter
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hψ : ψ ≠ 1 := by
    intro he
    apply hn
    rw [←χ.changeLevel_primitiveCharacter, show χ.primitiveCharacter = 1 from he,
      DirichletCharacter.changeLevel_one]
  have hc : (χ.conductor:ℝ) ≤ q := by
    exact_mod_cast Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level
  have hpow : (((q:ℝ)+2)*(|t|+2))^(-ε) ≤
      (((χ.conductor:ℝ)+2)*(|t|+2))^(-ε) :=
    Real.rpow_le_rpow_of_nonpos (by positivity)
      (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) (by linarith)
  have hp := h χ.conductor ψ χ.primitiveCharacter_isPrimitive hψ σ t
    (by nlinarith [mul_le_mul_of_nonneg_left hpow hA.le]) hσ2
  have hne : ψ.LFunction (σ+I*t) ≠ 0 := norm_pos_iff.mp
    (lt_of_lt_of_le (mul_pos hA (Real.rpow_pos_of_pos (by positivity) _)) hp)
  have hbase : 1 ≤ ((q:ℝ)+2)*(|t|+2) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) q, abs_nonneg t]
  have hpw := Real.rpow_le_one_of_one_le_of_nonpos hbase (show -ε ≤ 0 by linarith)
  have hσ0 : 0 < σ := by
    have hh := mul_le_of_le_one_right hA.le hpw
    linarith
  rw [←χ.changeLevel_primitiveCharacter,
    DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level ψ (Or.inl hψ)]
  apply mul_ne_zero hne
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hpn : ‖(p:ℂ)^(-((σ:ℂ)+I*t))‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hprime.pos]
    simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_self, add_zero]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hprime.one_lt) (by linarith)
  have hb : ‖ψ (p:ZMod χ.conductor)*(p:ℂ)^(-((σ:ℂ)+I*t))‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (ψ.norm_le_one _)).trans_lt hpn
  intro he
  have heq : ψ (p:ZMod χ.conductor)*(p:ℂ)^(-((σ:ℂ)+I*t)) = 1 := sub_eq_zero.mp he |>.symm
  rw [heq, norm_one] at hb
  exact lt_irrefl _ hb

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_ZetaPoleBranch
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A normalized analytic power of the pole-removed zeta function -/
namespace JointDickman
open Set

theorem norm_exp_real_mul_of_exp_eq (z : ℝ) {w v : ℂ} (he : Complex.exp w = v) :
    ‖Complex.exp ((z:ℂ)*w)‖ = ‖v‖^z := by
  rw [←he,Complex.norm_exp,Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero,←Real.exp_mul]
  congr 1
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.Rectangle
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}


lemma mem_Rect {z w : ℂ} (zRe_lt_wRe : z.re ≤ w.re) (zIm_lt_wIm : z.im ≤ w.im) (p : ℂ) :
    p ∈ Rectangle z w ↔
      z.re ≤ p.re ∧ p.re ≤ w.re ∧ z.im ≤ p.im ∧ p.im ≤ w.im := by
  rw [Rectangle, uIcc_of_le zRe_lt_wRe, uIcc_of_le zIm_lt_wIm]
  exact and_assoc
end

section
-- module Solutions.OAIQ083_JD.ResidueCalcOnRectangles
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

lemma verticalIntegral_split_three (a b : ℝ)
    (hf : Integrable (fun t : ℝ ↦ f (σ + t * I))) :
    VerticalIntegral f σ =
      I • (∫ t in Iic a, f (σ + t * I)) + VIntegral f σ a b +
      I • ∫ t in Ici b, f (σ + t * I) := by
  simp_rw [VerticalIntegral, VIntegral, ← smul_add]
  congr
  rw [← integral_Iic_sub_Iic hf.restrict hf.restrict, add_sub_cancel,
    integral_Iic_eq_integral_Iio, integral_Iio_add_Ici hf.restrict hf.restrict]

theorem HolomorphicOn.vanishesOnRectangle [CompleteSpace E]
    {U : Set ℂ} (f_holo : HolomorphicOn f U)
    (hU : Rectangle z w ⊆ U) :
    RectangleIntegral f z w = 0 :=
  integral_boundary_rect_eq_zero_of_differentiableOn f z w
    (f_holo.mono hU)

/-! ## Residue calculus: residues, simple poles, and the rectangle residue theorem

The simple-pole `residue`, `sumResiduesIn`, the `HasSimplePolesOn` scaffold, and the rectangle
residue theorem `RectangleIntegral'_eq_sumResiduesIn`. Extracted from `CH2.lean` as general,
reusable contour-integration lemmas (see issue #1537). -/
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_ZetaRectangleLog
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalized logarithms on the finite zero-free rectangles -/
namespace JointDickman
open Set

theorem zetaOpenRectangle_isOpen (δ T : ℝ) : IsOpen (zetaOpenRectangle δ T) :=
  (isOpen_Ioo.preimage Complex.continuous_re).inter (isOpen_Ioo.preimage Complex.continuous_im)

theorem zetaOpenRectangle_convex (δ T : ℝ) : Convex ℝ (zetaOpenRectangle δ T) :=
  ((convex_Ioo _ _).linear_preimage Complex.reLm).inter
    ((convex_Ioo _ _).linear_preimage Complex.imLm)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterRectangleLog
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Analytic logarithms on the character zero-free rectangles -/
namespace JointDickman
open Set

private theorem exists_analytic_log_with_value {U : Set ℂ}
    (hUc : IsSimplyConnected U) (hUo : IsOpen U) {x₀ v : ℂ} (hx₀ : x₀ ∈ U)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U) (hne : ∀ x ∈ U, g x ≠ 0)
    (hv : Complex.exp v = g x₀) :
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f U ∧ f x₀ = v ∧
      ∀ x ∈ U, Complex.exp (f x) = g x := by
  obtain ⟨f,hf,he⟩ := exists_analytic_log_on hUc hUo hg hne
  refine ⟨fun x => f x-f x₀+v, fun x hx => ((hf x hx).sub analyticAt_const).add
    analyticAt_const, by simp, ?_⟩
  intro x hx
  rw [Complex.exp_add, Complex.exp_sub, he x hx, he x₀ hx₀, hv,
    div_mul_cancel₀ _ (hne x₀ hx₀)]

/-- A normalized logarithm exists uniformly on rectangles with a power-sized width. -/
theorem character_rectangle_log {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ A : ℝ, 0 < A ∧ A ≤ 1/4 ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ T : ℝ, 0 < T → ∀ v : ℂ, Complex.exp v = χ.LFunction (3/2) →
      ∃ f : ℂ → ℂ,
        AnalyticOnNhd ℂ f (zetaOpenRectangle (characterContourWidth A ε q T) T) ∧
        f (3/2) = v ∧ ∀ s ∈ zetaOpenRectangle (characterContourWidth A ε q T) T,
          Complex.exp (f s) = χ.LFunction s := by
  obtain ⟨A,hA,hA4,hzero⟩ := nonprincipal_character_zero_free_strip hε hε1
  refine ⟨A,hA,hA4,?_⟩
  intro q _ χ hn T hT v hv
  have hw : 0 < characterContourWidth A ε q T := by
    dsimp [characterContourWidth]
    exact mul_pos hA (Real.rpow_pos_of_pos (by positivity) _)
  have hx : (3/2:ℂ) ∈ zetaOpenRectangle (characterContourWidth A ε q T) T := by
    constructor <;> constructor <;> norm_num <;> linarith
  let : ContractibleSpace (zetaOpenRectangle (characterContourWidth A ε q T) T) :=
    (zetaOpenRectangle_convex _ _).contractibleSpace ⟨3/2,hx⟩
  have hsimp : IsSimplyConnected (zetaOpenRectangle (characterContourWidth A ε q T) T) := by
    change SimplyConnectedSpace _
    infer_instance
  apply exists_analytic_log_with_value hsimp (zetaOpenRectangle_isOpen _ _) hx
    (fun s _ => (DirichletCharacter.differentiable_LFunction hn).analyticAt s) ?_ hv
  intro s hs
  have habs : |s.im| ≤ T := abs_le.mpr ⟨hs.2.1.le,hs.2.2.le⟩
  have hpow : (((q:ℝ)+2)*(T+2))^(-ε) ≤ (((q:ℝ)+2)*(|s.im|+2))^(-ε) :=
    Real.rpow_le_rpow_of_nonpos (by positivity)
      (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) (by linarith)
  have hlo : 1-A*(((q:ℝ)+2)*(|s.im|+2))^(-ε) ≤ s.re := by
    have hh := mul_le_mul_of_nonneg_left hpow hA.le
    have hh' := hs.1.1
    change 1-A*(((q:ℝ)+2)*(T+2))^(-ε) < s.re at hh'
    linarith
  have hne := hzero q χ hn s.re s.im hlo hs.1.2.le
  have he : (s.re:ℂ)+Complex.I*(s.im:ℂ) = s := by
    simpa only [mul_comm Complex.I] using Complex.re_add_im s
  rwa [he] at hne

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughConvolution
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact removal of the small prime factors

Removing a finite set of prime factors is an exact convolution identity.
The moving roughness cutoff is then controlled by Selberg–Delange estimates.
-/

namespace JointDickman

open ArithmeticFunction Finset

theorem squarefreeWeight_isMultiplicative (z : ℝ) :
    (squarefreeWeight z).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨squarefreeWeight_one z, fun {m n} hm hn hmn => ?_⟩
  simp only [squarefreeWeight, coe_mk, Nat.squarefree_mul hmn,
    ite_zero_mul_ite_zero, cardFactors_mul hm hn, pow_add]

theorem squarefreeWeight_prime_pow (z : ℝ) {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    squarefreeWeight z (p ^ k) = if k = 1 then z else 0 := by
  by_cases hk1 : k = 1
  · simp [hk1, squarefreeWeight, hp.squarefree, cardFactors_apply_prime hp]
  · have hsq : ¬Squarefree (p ^ k) := by
      rw [Nat.squarefree_pow_iff hp.ne_one hk]
      simp [hk1]
    simp [squarefreeWeight, hsq, hk1]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreeDirichletSeries
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The squarefree Dirichlet series and its Euler product

These identities begin the analytic discharge of the two fixed-exponent
Selberg–Delange expansions. They do not assume an asymptotic for the
coefficients.
-/
namespace JointDickman
open Finset ArithmeticFunction

 theorem squarefreeWeight_abs_le_one_dup1 {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (n : ℕ) :
    |squarefreeWeight z n| ≤ 1 := by
  simp only [squarefreeWeight,coe_mk]
  split_ifs
  · rw [abs_of_nonneg (pow_nonneg hz _)]
    exact pow_le_one₀ hz hz1
  · norm_num

 theorem squarefreeDirichletSummand_term (z : ℝ) (s : ℂ) (n : ℕ) :
    squarefreeDirichletSummand z s n = LSeries.term (fun n => (squarefreeWeight z n : ℂ)) s n := by
  rw [LSeries.term_def₀ (by simp : (squarefreeWeight z 0 : ℂ) = 0)]
  rfl

 theorem squarefreeDirichletSummand_zero (z : ℝ) (s : ℂ) : squarefreeDirichletSummand z s 0 = 0 := by
  simp [squarefreeDirichletSummand]

 theorem squarefreeDirichletSummand_one (z : ℝ) (s : ℂ) : squarefreeDirichletSummand z s 1 = 1 := by
  simp [squarefreeDirichletSummand]

 theorem squarefreeDirichletSummand_mul (z : ℝ) (s : ℂ) {m n : ℕ} (hmn : m.Coprime n) :
    squarefreeDirichletSummand z s (m*n) =
      squarefreeDirichletSummand z s m * squarefreeDirichletSummand z s n := by
  unfold squarefreeDirichletSummand
  rw [(squarefreeWeight_isMultiplicative z).2 hmn]
  push_cast
  rw [← Complex.ofReal_natCast m, ← Complex.ofReal_natCast n,
    Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
  ring

 theorem squarefreeDirichletSummand_summable {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    {s : ℂ} (hs : 1 < s.re) : Summable (fun n => ‖squarefreeDirichletSummand z s n‖) := by
  have h : LSeriesSummable (fun n => (squarefreeWeight z n : ℂ)) s :=
    LSeriesSummable_of_bounded_of_one_lt_re
      (fun n _ => by simpa only [Complex.norm_real,Real.norm_eq_abs] using squarefreeWeight_abs_le_one_dup1 hz hz1 n) hs
  simpa only [squarefreeDirichletSummand_term] using h.norm

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SquarefreeEulerLog
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quadratic cancellation in the squarefree Euler logarithm -/
namespace JointDickman

 theorem complex_log_error_bound {v : ℂ} {r : ℝ} (hr : r < 1) (hv : ‖v‖ ≤ r) :
    ‖Complex.log (1+v)-v‖ ≤ ‖v‖^2/(1-r) := by
  have hv1 : ‖v‖ < 1 := hv.trans_lt hr
  have hinv : (1-‖v‖)⁻¹ ≤ (1-r)⁻¹ := inv_anti₀ (by linarith) (by linarith)
  calc
    _ ≤ ‖v‖^2*(1-‖v‖)⁻¹/2 := Complex.norm_log_one_add_sub_self_le hv1
    _ ≤ ‖v‖^2*(1-‖v‖)⁻¹ := div_le_self (by positivity) (by norm_num)
    _ ≤ ‖v‖^2*(1-r)⁻¹ := mul_le_mul_of_nonneg_left hinv (sq_nonneg _)
    _ = _ := rfl

 theorem squarefreeEulerLog_norm_bound {z r : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hr : r < 1) {w : ℂ} (hw : ‖w‖ ≤ r) :
    ‖squarefreeEulerLog z w‖ ≤ 2*‖w‖^2/(1-r) := by
  have hzw : ‖(z:ℂ)*w‖ ≤ ‖w‖ := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hz]
    exact mul_le_of_le_one_left (norm_nonneg _) hz1
  have hv := complex_log_error_bound hr (hzw.trans hw)
  have hm := complex_log_error_bound hr (show ‖-w‖ ≤ r by simpa only [norm_neg] using hw)
  have heq : squarefreeEulerLog z w = (Complex.log (1+(z:ℂ)*w)-(z:ℂ)*w)+
      (z:ℂ)*(Complex.log (1-w)+w) := by unfold squarefreeEulerLog; ring
  rw [heq]
  have hq : 0 ≤ ‖w‖^2/(1-r) := by positivity
  calc
    _ ≤ ‖Complex.log (1+(z:ℂ)*w)-(z:ℂ)*w‖+
        ‖(z:ℂ)*(Complex.log (1-w)+w)‖ := norm_add_le _ _
    _ ≤ ‖w‖^2/(1-r)+‖w‖^2/(1-r) := by
      apply add_le_add
      · exact hv.trans (div_le_div_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hzw) (by linarith))
      · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hz]
        have hm' : ‖Complex.log (1-w)+w‖ ≤ ‖w‖^2/(1-r) := by
          simpa only [norm_neg,sub_neg_eq_add,← sub_eq_add_neg] using hm
        exact (mul_le_mul_of_nonneg_left hm' hz).trans (mul_le_of_le_one_left hq hz1)
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreeEulerAnalytic
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The analytic Euler correction in the half-plane Re(s) > 1/2 -/
namespace JointDickman
open scoped Topology

 theorem prime_negative_cpow_norm_le {σ : ℝ} (hσ : 0 ≤ σ) {s : ℂ} (hs : σ ≤ s.re)
    (p : Nat.Primes) : ‖(p.val:ℂ)^(-s)‖ ≤ (2:ℝ)^(-σ) := by
  rw [Complex.norm_natCast_cpow_of_pos p.property.pos,Complex.neg_re]
  calc
    _ ≤ (p.val:ℝ)^(-σ) := Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast p.property.one_le) (by linarith)
    _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by norm_num)
      (by exact_mod_cast p.property.two_le) (by linarith)

 theorem squarefreePrimeLog_bound_summable {σ : ℝ} (hσ : 1/2 < σ) :
    Summable (fun p : Nat.Primes => (2/(1-(2:ℝ)^(-σ)))*(p.val:ℝ)^(-2*σ)) := by
  have hsum : Summable (fun n : ℕ => (n:ℝ)^(-2*σ)) := Real.summable_nat_rpow.mpr (by linarith)
  exact (hsum.subtype Nat.Prime).mul_left _

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreeCharacterEuler
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The absolutely convergent Euler correction for squarefree character sums -/
namespace JointDickman

theorem characterPrimePower_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (p : Nat.Primes) :
    ‖characterPrimePower χ s p‖ ≤ ‖(p.val:ℂ)^(-s)‖ := by
  rw [characterPrimePower, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)

theorem squarefreeCharacterPrimeLog_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    {z σ : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (hσ : 0 < σ)
    {s : ℂ} (hs : σ ≤ s.re) (p : Nat.Primes) :
    ‖squarefreeCharacterPrimeLog χ z s p‖ ≤
      (2/(1-(2:ℝ)^(-σ)))*(p.val:ℝ)^(-2*σ) := by
  have hr : (2:ℝ)^(-σ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hnorm := (characterPrimePower_norm_le χ p).trans
    (prime_negative_cpow_norm_le hσ.le hs p)
  have hn : ‖characterPrimePower χ s p‖ ≤ (p.val:ℝ)^(-σ) := by
    apply (characterPrimePower_norm_le χ p).trans
    rw [Complex.norm_natCast_cpow_of_pos p.property.pos, Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.property.one_le) (by linarith)
  calc
    _ ≤ 2*‖characterPrimePower χ s p‖^2/(1-(2:ℝ)^(-σ)) :=
      squarefreeEulerLog_norm_bound hz hz1 hr hnorm
    _ ≤ 2*((p.val:ℝ)^(-σ))^2/(1-(2:ℝ)^(-σ)) := by
      apply div_le_div_of_nonneg_right _ (by linarith)
      exact mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)).mpr hn)
        (by norm_num)
    _ = _ := by
      rw [←Real.rpow_natCast, ←Real.rpow_mul (Nat.cast_nonneg p.val)]
      norm_num only [Nat.cast_ofNat]
      rw [show -σ*(2:ℝ) = -2*σ by ring]
      ring

theorem squarefreeCharacterPrimeLog_summable {q : ℕ} (χ : DirichletCharacter ℂ q)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) {s : ℂ} (hs : 1/2 < s.re) :
    Summable (fun p : Nat.Primes => squarefreeCharacterPrimeLog χ z s p) := by
  apply Summable.of_norm
  exact (squarefreePrimeLog_bound_summable hs).of_nonneg_of_le
    (fun p => norm_nonneg _) (fun p => squarefreeCharacterPrimeLog_bound χ hz hz1
      (by linarith) le_rfl p)

theorem squarefreeCharacterPrimeLog_differentiableAt {q : ℕ}
    (χ : DirichletCharacter ℂ q) {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    {s : ℂ} (hs : 0 < s.re) (p : Nat.Primes) :
    DifferentiableAt ℂ (fun t => squarefreeCharacterPrimeLog χ z t p) s := by
  have hw : ‖characterPrimePower χ s p‖ < 1 :=
    ((characterPrimePower_norm_le χ p).trans (prime_negative_cpow_norm_le hs.le le_rfl p)).trans_lt
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  have hzw : ‖(z:ℂ)*characterPrimePower χ s p‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hz]
    exact (mul_le_of_le_one_left (norm_nonneg _) hz1).trans_lt hw
  have hp0 : (p.val:ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hf : DifferentiableAt ℂ (fun t => characterPrimePower χ t p) s :=
    (differentiableAt_id.neg.const_cpow (Or.inl hp0)).const_mul _
  have h₁ := ((differentiableAt_const (1:ℂ)).add
    ((differentiableAt_const (z:ℂ)).mul hf)).clog (Complex.mem_slitPlane_of_norm_lt_one hzw)
  have hslit : 1-characterPrimePower χ s p ∈ Complex.slitPlane := by
    have hh : ‖-characterPrimePower χ s p‖ < 1 := by simpa only [norm_neg] using hw
    simpa only [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one hh
  exact h₁.add ((differentiableAt_const (z:ℂ)).mul
    (((differentiableAt_const (1:ℂ)).sub hf).clog hslit))

theorem squarefreeCharacterLogFactor_differentiableOn {q : ℕ}
    (χ : DirichletCharacter ℂ q) {z σ : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hσ : 1/2 < σ) :
    DifferentiableOn ℂ (squarefreeCharacterLogFactor χ z) {s : ℂ | σ < s.re} := by
  apply Complex.differentiableOn_tsum_of_summable_norm (squarefreePrimeLog_bound_summable hσ)
  · intro p s hs
    exact (squarefreeCharacterPrimeLog_differentiableAt χ hz hz1
      (by dsimp at hs <;> linarith) p).differentiableWithinAt
  · exact isOpen_lt continuous_const Complex.continuous_re
  · intro p s hs
    exact squarefreeCharacterPrimeLog_bound χ hz hz1 (by linarith) hs.le p

theorem squarefreeCharacterLogFactor_analyticOnNhd {q : ℕ}
    (χ : DirichletCharacter ℂ q) {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    AnalyticOnNhd ℂ (squarefreeCharacterLogFactor χ z) {s : ℂ | 1/2 < s.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro s hs
  have hσ : 1/2 < (s.re+1/2)/2 := by dsimp at hs <;> linarith
  have hmem : s ∈ {t : ℂ | (s.re+1/2)/2 < t.re} := by dsimp at hs ⊢; linarith
  have hopen : IsOpen {t : ℂ | (s.re+1/2)/2 < t.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  exact ((squarefreeCharacterLogFactor_differentiableOn χ hz hz1 hσ).differentiableAt
    (hopen.mem_nhds hmem)).differentiableWithinAt

theorem squarefreeCharacterAnalyticFactor_analyticOnNhd {q : ℕ}
    (χ : DirichletCharacter ℂ q) {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    AnalyticOnNhd ℂ (squarefreeCharacterAnalyticFactor χ z) {s : ℂ | 1/2 < s.re} :=
  (squarefreeCharacterLogFactor_analyticOnNhd χ hz hz1).cexp

theorem squarefreeCharacterAnalyticFactor_uniform_bound {z σ : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hσ : 1/2 < σ) : ∃ C : ℝ, 0 < C ∧
    ∀ {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ), σ ≤ s.re →
      ‖squarefreeCharacterAnalyticFactor χ z s‖ ≤ C := by
  let b : Nat.Primes → ℝ := fun p => (2/(1-(2:ℝ)^(-σ)))*(p.val:ℝ)^(-2*σ)
  have hb : Summable b := squarefreePrimeLog_bound_summable hσ
  refine ⟨Real.exp (∑' p, b p),Real.exp_pos _,fun χ s hs => ?_⟩
  have hf := squarefreeCharacterPrimeLog_summable χ hz hz1 (hσ.trans_le hs)
  have hl : ‖squarefreeCharacterLogFactor χ z s‖ ≤ ∑' p, b p := by
    calc
      _ ≤ ∑' p, ‖squarefreeCharacterPrimeLog χ z s p‖ := norm_tsum_le_tsum_norm hf.norm
      _ ≤ _ := hf.norm.tsum_le_tsum
        (fun p => squarefreeCharacterPrimeLog_bound χ hz hz1 (by linarith) hs p) hb
  exact (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr hl)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreeCharacterDirichletSeries
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Euler products of the character-twisted squarefree coefficients -/
namespace JointDickman
open Finset

theorem squarefreeCharacterDirichletSummand_term {q : ℕ}
    (χ : DirichletCharacter ℂ q) (z : ℝ) (s : ℂ) (n : ℕ) :
    squarefreeCharacterDirichletSummand χ z s n =
      LSeries.term (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) s n := by
  rw [LSeries.term_def₀ (f := fun n : ℕ => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) (by simp)]
  dsimp [squarefreeCharacterDirichletSummand, squarefreeDirichletSummand]
  ring

theorem squarefreeCharacterDirichletSummand_summable {q : ℕ}
    (χ : DirichletCharacter ℂ q) {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n => ‖squarefreeCharacterDirichletSummand χ z s n‖) := by
  apply (squarefreeDirichletSummand_summable hz hz1 hs).of_nonneg_of_le
    (fun n => norm_nonneg _)
  intro n
  rw [squarefreeCharacterDirichletSummand, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (χ.norm_le_one _)

theorem squarefreeCharacterDirichletSeries_eulerProduct {q : ℕ}
    (χ : DirichletCharacter ℂ q) {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => 1+(z:ℂ)*characterPrimePower χ s p)
      (LSeries (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) s) := by
  have hmul {m n : ℕ} (hmn : m.Coprime n) :
      squarefreeCharacterDirichletSummand χ z s (m*n) =
        squarefreeCharacterDirichletSummand χ z s m *
        squarefreeCharacterDirichletSummand χ z s n := by
    rw [squarefreeCharacterDirichletSummand, squarefreeDirichletSummand_mul z s hmn]
    simp only [Nat.cast_mul, map_mul, squarefreeCharacterDirichletSummand]
    ring
  have hone : squarefreeCharacterDirichletSummand χ z s 1 = 1 := by
    simp [squarefreeCharacterDirichletSummand, squarefreeDirichletSummand_one]
  have hzero : squarefreeCharacterDirichletSummand χ z s 0 = 0 := by
    simp [squarefreeCharacterDirichletSummand, squarefreeDirichletSummand_zero]
  have h := EulerProduct.eulerProduct_hasProd hone (fun {m n} hmn => hmul hmn)
    (squarefreeCharacterDirichletSummand_summable χ hz hz1 hs) hzero
  have he (p : Nat.Primes) :
      (∑' e : ℕ, squarefreeCharacterDirichletSummand χ z s (p.val^e)) =
        1+(z:ℂ)*characterPrimePower χ s p := by
    have hpw : squarefreeWeight z p.val = z := by
      simpa only [pow_one, ite_true, if_true] using
        squarefreeWeight_prime_pow z p.property (by omega : (1:ℕ) ≠ 0)
    rw [tsum_eq_sum (s := {0,1})]
    · simp [squarefreeCharacterDirichletSummand, squarefreeDirichletSummand,
        hpw, characterPrimePower]
      ring
    · intro e he
      have he0 : e ≠ 0 := by intro h; apply he; simp [h]
      have he1 : e ≠ 1 := by intro h; apply he; simp [h]
      simp [squarefreeCharacterDirichletSummand, squarefreeDirichletSummand,
        squarefreeWeight_prime_pow z p.property he0, he1]
  rw [show (fun p : Nat.Primes => ∑' e : ℕ,
    squarefreeCharacterDirichletSummand χ z s (p.val^e)) =
      (fun p => 1+(z:ℂ)*characterPrimePower χ s p) from funext he] at h
  simpa only [squarefreeCharacterDirichletSummand_term, LSeries] using h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreeCharacterFactorization
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Analytic factorization of the twisted squarefree Dirichlet series -/
namespace JointDickman

theorem primeCharacterLog_summable {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes => -Complex.log (1-characterPrimePower χ s p)) := by
  convert! (summable_dirichletSummand χ hs).of_norm.clog_one_sub.neg.subtype Nat.Prime using 1
  all_goals try with_reducible_and_instances rfl

theorem primeCharacterLog_exp {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) : Complex.exp (primeCharacterLog χ s) = χ.LFunction s := by
  rw [χ.LFunction_eq_LSeries hs]
  exact χ.LSeries_eulerProduct_exp_log hs

theorem primeCharacterLog_summand_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) {s : ℂ} (hs : σ ≤ s.re) (p : Nat.Primes) :
    ‖-Complex.log (1-characterPrimePower χ s p)‖ ≤ (3/2:ℝ)*(p.val:ℝ)^(-σ) := by
  have hhalf : ‖characterPrimePower χ s p‖ ≤ 1/2 :=
    (characterPrimePower_norm_le χ p).trans
      (Complex.norm_prime_cpow_le_one_half p (hσ.trans_le hs))
  have hh := Complex.norm_log_one_add_half_le_self
    (z := -characterPrimePower χ s p) (by simpa only [norm_neg] using hhalf)
  rw [norm_neg]
  calc
    _ ≤ (3/2:ℝ)*‖characterPrimePower χ s p‖ := by
      simpa only [sub_eq_add_neg, norm_neg] using hh
    _ ≤ (3/2:ℝ)*‖(p.val:ℂ)^(-s)‖ :=
      mul_le_mul_of_nonneg_left (characterPrimePower_norm_le χ p) (by norm_num)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [Complex.norm_natCast_cpow_of_pos p.property.pos, Complex.neg_re]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.property.one_le) (by linarith)

theorem primeCharacterLog_differentiableOn {q : ℕ} (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) :
    DifferentiableOn ℂ (primeCharacterLog χ) {s : ℂ | σ < s.re} := by
  have hsum : Summable (fun p : Nat.Primes => (3/2:ℝ)*(p.val:ℝ)^(-σ)) :=
    ((Real.summable_nat_rpow.mpr (by linarith : -σ < -1)).subtype Nat.Prime).mul_left _
  apply Complex.differentiableOn_tsum_of_summable_norm hsum
  · intro p s hs
    have hw : ‖-characterPrimePower χ s p‖ < 1 := by
      rw [norm_neg]
      exact ((characterPrimePower_norm_le χ p).trans
        (Complex.norm_prime_cpow_le_one_half p (by dsimp at hs <;> linarith))).trans_lt (by norm_num)
    have hc : DifferentiableAt ℂ (fun t => characterPrimePower χ t p) s :=
      (differentiableAt_id.neg.const_cpow (Or.inl
        (by exact_mod_cast p.property.ne_zero))).const_mul _
    exact (((differentiableAt_const (1:ℂ)).sub hc).clog
      (by simpa only [Pi.add_apply, Pi.neg_apply, sub_eq_add_neg] using
        Complex.mem_slitPlane_of_norm_lt_one hw)).neg.differentiableWithinAt
  · exact isOpen_lt continuous_const Complex.continuous_re
  · intro p s hs
    exact primeCharacterLog_summand_bound χ hσ hs.le p

theorem primeCharacterLog_analyticOnNhd {q : ℕ} (χ : DirichletCharacter ℂ q) :
    AnalyticOnNhd ℂ (primeCharacterLog χ) {s : ℂ | 1 < s.re} := by
  intro s hs
  have hσ : 1 < (1+s.re)/2 := by dsimp at hs <;> linarith
  have hm : s ∈ {t : ℂ | (1+s.re)/2 < t.re} := by dsimp at hs ⊢; linarith
  exact (primeCharacterLog_differentiableOn χ hσ).analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re) s hm

theorem squarefreeCharacterDirichletSeries_factorization {q : ℕ}
    (χ : DirichletCharacter ℂ q) {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) s =
      squarefreeCharacterAnalyticFactor χ z s * Complex.exp ((z:ℂ)*primeCharacterLog χ s) := by
  have hG := squarefreeCharacterPrimeLog_summable χ hz hz1 (show 1/2 < s.re by linarith)
  have hZ := (primeCharacterLog_summable χ hs).mul_left (z:ℂ)
  have hsum := (hG.add hZ).hasSum.cexp
  rw [Summable.tsum_add hG hZ, tsum_mul_left, Complex.exp_add] at hsum
  have heq (p : Nat.Primes) :
      Complex.exp (squarefreeCharacterPrimeLog χ z s p+
        (z:ℂ)*(-Complex.log (1-characterPrimePower χ s p))) =
      1+(z:ℂ)*characterPrimePower χ s p := by
    have hn : ‖(z:ℂ)*characterPrimePower χ s p‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hz]
      exact (mul_le_of_le_one_left (norm_nonneg _) hz1).trans_lt
        (((characterPrimePower_norm_le χ p).trans
          (Complex.norm_prime_cpow_le_one_half p hs)).trans_lt (by norm_num))
    have hne : 1+(z:ℂ)*characterPrimePower χ s p ≠ 0 := by
      intro he
      have hv : (z:ℂ)*characterPrimePower χ s p = -1 := by linear_combination he
      rw [hv, norm_neg, norm_one] at hn
      exact lt_irrefl _ hn
    have hcancel : squarefreeCharacterPrimeLog χ z s p+
        (z:ℂ)*(-Complex.log (1-characterPrimePower χ s p)) =
        Complex.log (1+(z:ℂ)*characterPrimePower χ s p) := by
      unfold squarefreeCharacterPrimeLog squarefreeEulerLog
      ring
    rw [hcancel, Complex.exp_log hne]
  have hp : HasProd (fun p : Nat.Primes => 1+(z:ℂ)*characterPrimePower χ s p)
      (squarefreeCharacterAnalyticFactor χ z s * Complex.exp ((z:ℂ)*primeCharacterLog χ s)) := by
    have hf : (Complex.exp ∘ (fun p : Nat.Primes => squarefreeCharacterPrimeLog χ z s p+
        (z:ℂ)*(-Complex.log (1-characterPrimePower χ s p)))) =
        (fun p => 1+(z:ℂ)*characterPrimePower χ s p) := funext heq
    rw [hf] at hsum
    simpa only [squarefreeCharacterAnalyticFactor, squarefreeCharacterLogFactor,
      primeCharacterLog] using hsum
  exact (squarefreeCharacterDirichletSeries_eulerProduct χ hz hz1 hs).unique hp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterContourSeries
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying the continued character series on the Perron line -/
namespace JointDickman
open Set

theorem character_rectangle_log_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {δ T : ℝ} (hδ : 0 < δ) (hT : 0 < T) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (zetaOpenRectangle δ T))
    (hf0 : f (3/2) = primeCharacterLog χ (3/2))
    (he : ∀ s ∈ zetaOpenRectangle δ T, Complex.exp (f s) = χ.LFunction s) :
    EqOn f (primeCharacterLog χ) (zetaOpenRectangle 0 T) := by
  have hsub : zetaOpenRectangle 0 T ⊆ zetaOpenRectangle δ T := by
    intro s hs
    have hh : 1 < s.re := by simpa using hs.1.1
    exact ⟨⟨by linarith, hs.1.2⟩, hs.2⟩
  have hx : (3/2:ℂ) ∈ zetaOpenRectangle 0 T := by
    constructor <;> constructor <;> norm_num <;> linarith
  apply analytic_log_unique (zetaOpenRectangle_isOpen 0 T)
    (zetaOpenRectangle_convex 0 T).isPreconnected (hf.mono hsub)
    (fun s hs => primeCharacterLog_analyticOnNhd χ s (by simpa using hs.1.1))
    (fun s hs => (he s (hsub hs)).trans (primeCharacterLog_exp χ
      (by simpa using hs.1.1)).symm) hx hf0

theorem characterContourSeries_eq_LSeries {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {z δ T : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (hδ : 0 < δ) (hT : 0 < T)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (zetaOpenRectangle δ T))
    (hf0 : f (3/2) = primeCharacterLog χ (3/2))
    (he : ∀ s ∈ zetaOpenRectangle δ T, Complex.exp (f s) = χ.LFunction s)
    {s : ℂ} (hs : s ∈ zetaOpenRectangle 0 T) :
    characterContourSeries χ z f s =
      LSeries (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) s := by
  rw [characterContourSeries, character_rectangle_log_eq χ hδ hT hf hf0 he hs]
  exact (squarefreeCharacterDirichletSeries_factorization χ hz hz1 (by simpa using hs.1.1)).symm

theorem characterContourSeries_analyticOnNhd {q : ℕ} (χ : DirichletCharacter ℂ q)
    {z δ T : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (hδ : δ ≤ 1/4)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (zetaOpenRectangle δ T)) :
    AnalyticOnNhd ℂ (characterContourSeries χ z f) (zetaOpenRectangle δ T) := by
  intro s hs
  have hre : 1/2 < s.re := by have hh : 1-δ < s.re := hs.1.1; linarith
  exact (squarefreeCharacterAnalyticFactor_analyticOnNhd χ hz hz1 s hre).mul
    ((analyticAt_const.mul (hf s hs)).cexp)

theorem characterContourSeries_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {z σ C : ℝ} {f : ℂ → ℂ}
    (hG : ∀ s : ℂ, σ ≤ s.re → ‖squarefreeCharacterAnalyticFactor χ z s‖ ≤ C)
    {s : ℂ} (hs : σ ≤ s.re) (he : Complex.exp (f s) = χ.LFunction s) :
    ‖characterContourSeries χ z f s‖ ≤ C * ‖χ.LFunction s‖^z := by
  rw [characterContourSeries, norm_mul, norm_exp_real_mul_of_exp_eq z he]
  exact mul_le_mul_of_nonneg_right (hG s hs) (Real.rpow_nonneg (norm_nonneg _) _)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterContourBounds
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Small-power bounds for the continued character series -/
namespace JointDickman
open Complex

theorem characterContourSeries_small_power {z η : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1/4) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ ≠ 1 → ∀ (f : ℂ → ℂ) (s : ℂ), 1-η/2 ≤ s.re →
      Complex.exp (f s) = χ.LFunction s →
      ‖characterContourSeries χ z f s‖ ≤ C * (((q:ℝ)+2)*(‖s‖+2))^η := by
  obtain ⟨G,hG,hGb⟩ := squarefreeCharacterAnalyticFactor_uniform_bound hz hz1
    (by norm_num : (1/2:ℝ) < 3/4)
  obtain ⟨K,hK,hKb⟩ := LargePrimeGaps.LFunction_norm_small_power
    (show 0 < η/2 by positivity) (show η/2 ≤ 1/2 by linarith)
  let B := max 1 K
  have hB : 1 ≤ B := le_max_left _ _
  refine ⟨G*B, mul_pos hG (lt_of_lt_of_le zero_lt_one hB), ?_⟩
  intro q _ χ hn f s hs he
  let W : ℝ := ((q:ℝ)+2)*(‖s‖+2)
  have hW : 1 ≤ W := by dsimp [W] <;> nlinarith [Nat.cast_nonneg (α := ℝ) q, norm_nonneg s]
  have hWp : 1 ≤ W^η := Real.one_le_rpow hW hη.le
  have hBW : 1 ≤ B*W^η := one_le_mul_of_one_le_of_one_le hB hWp
  have hL : ‖χ.LFunction s‖ ≤ B*W^η := by
    have hb := hKb q χ hn s hs
    rw [show 2*(η/2) = η by ring] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (le_max_right 1 K) (Real.rpow_nonneg (by linarith) _))
  calc
    _ ≤ G*‖χ.LFunction s‖^z := characterContourSeries_norm_le χ
      (fun t ht => hGb χ t ht) (by linarith) he
    _ ≤ G*(B*W^η)^z := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) hL hz) hG.le
    _ ≤ G*(B*W^η) := mul_le_mul_of_nonneg_left (Real.rpow_le_self_of_one_le hBW hz1) hG.le
    _ = (G*B)*W^η := by ring

/-- On a fixed-height rectangle the bound depends on the height and modulus only. -/
theorem characterContourSeries_rectangle_bound {z η : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1/4) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ ≠ 1 → ∀ (f : ℂ → ℂ) (T : ℝ), 0 ≤ T → ∀ s : ℂ,
      1-η/2 ≤ s.re → s.re ≤ 2 → |s.im| ≤ T →
      Complex.exp (f s) = χ.LFunction s →
      ‖characterContourSeries χ z f s‖ ≤ C * (((q:ℝ)+2)*(T+2))^η := by
  obtain ⟨C,hC,hb⟩ := characterContourSeries_small_power hz hz1 hη hη1
  refine ⟨C*2^η, by positivity, ?_⟩
  intro q _ χ hn f T hT s hs hs2 hi he
  have hs0 : 0 ≤ s.re := by linarith
  have hnS : ‖s‖+2 ≤ 2*(T+2) := by
    have hh := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_nonneg hs0] at hh
    linarith
  have hbase : ((q:ℝ)+2)*(‖s‖+2) ≤ 2*(((q:ℝ)+2)*(T+2)) := by
    nlinarith [mul_le_mul_of_nonneg_left hnS (show (0:ℝ) ≤ q+2 by positivity)]
  calc
    _ ≤ C*(((q:ℝ)+2)*(‖s‖+2))^η := hb q χ hn f s hs he
    _ ≤ C*(2*(((q:ℝ)+2)*(T+2)))^η := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hbase hη.le) hC.le
    _ = (C*2^η)*(((q:ℝ)+2)*(T+2))^η := by
      rw [Real.mul_rpow (by norm_num) (by positivity)]
      ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_RieszDenominatorBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform integrable bounds for the Riesz--Perron denominator -/
namespace JointDickman

theorem rieszDenominator_im_lower_bound (s : ℂ) :
    s.im^2 ≤ ‖s‖*‖s+1‖ := by
  have h1 := Complex.abs_im_le_norm s
  have h2 : |s.im| ≤ ‖s+1‖ := by simpa using Complex.abs_im_le_norm (s+1)
  have h := mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
  nlinarith [sq_abs s.im]

theorem rieszDenominator_lower_bound {s : ℂ} (hs : 1/2 ≤ s.re) :
    (1+s.im^2)/5 ≤ ‖s‖*‖s+1‖ := by
  have h1 : (1/2:ℝ) ≤ ‖s‖ := hs.trans ((le_abs_self _).trans (Complex.abs_re_le_norm s))
  have h2 : (1/2:ℝ) ≤ ‖s+1‖ := by
    have h := Complex.abs_re_le_norm (s+1)
    have hle := le_abs_self (s+1).re
    simp only [Complex.add_re,Complex.one_re] at h hle
    linarith
  have hprod : (1/2:ℝ)*(1/2) ≤ ‖s‖*‖s+1‖ :=
    mul_le_mul h1 h2 (by norm_num) (norm_nonneg _)
  nlinarith [rieszDenominator_im_lower_bound s]

theorem rieszDenominator_inv_bound {s : ℂ} (hs : 1/2 ≤ s.re) :
    1/(‖s‖*‖s+1‖) ≤ 5/(1+s.im^2) := by
  have hp : 0 < (1+s.im^2)/5 := by positivity
  have h := one_div_le_one_div_of_le hp (rieszDenominator_lower_bound hs)
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_RieszContourBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrable majorants for the squarefree Riesz contour -/
namespace JointDickman
open Complex Set MeasureTheory

theorem verticalIntegral_bound_by_cauchy {f : ℂ → ℂ} {σ T D : ℝ}
    (hT : 0 ≤ T) (hD : 0 ≤ D)
    (hf : ∀ t ∈ Ioc (-T) T, ‖f ((σ:ℂ)+(t:ℂ)*I)‖ ≤ D/(1+t^2)) :
    ‖VIntegral f σ (-T) T‖ ≤ D*Real.pi := by
  have hi : Integrable (fun t : ℝ => D/(1+t^2)) := by
    simpa only [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul D
  rw [VIntegral,norm_smul,Complex.norm_I,one_mul,
    intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  calc
    _ ≤ ∫ t : ℝ in Ioc (-T) T, D/(1+t^2) := by
      apply norm_integral_le_of_norm_le hi.restrict
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hf t ht
    _ ≤ ∫ t : ℝ, D/(1+t^2) := by
      apply setIntegral_le_integral hi
      filter_upwards with t
      positivity
    _ = D*Real.pi := by
      simp only [div_eq_mul_inv,integral_const_mul,integral_univ_inv_one_add_sq]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterRieszKernel
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The regular character Riesz kernel and its vertical bound -/
namespace JointDickman
open Complex Set MeasureTheory

theorem characterRieszKernel_norm {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z L : ℝ) (f : ℂ → ℂ) (w : ℂ) :
    ‖characterRieszKernel χ z L f w‖ =
      ‖characterContourSeries χ z f (1+w)‖ * Real.exp (L*w.re) / (‖1+w‖*‖2+w‖) := by
  simp only [characterRieszKernel, norm_div, norm_mul, Complex.norm_exp,
    mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]

theorem characterRieszKernel_point_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    {z L B : ℝ} {f : ℂ → ℂ} {w : ℂ}
    (hB : 0 ≤ B) (hs : 1/2 ≤ (1+w).re)
    (hb : ‖characterContourSeries χ z f (1+w)‖ ≤ B) :
    ‖characterRieszKernel χ z L f w‖ ≤ 5*B*Real.exp (L*w.re)/(1+w.im^2) := by
  have hd : 1/(‖1+w‖*‖2+w‖) ≤ 5/(1+w.im^2) := by
    simpa only [add_im, one_im, zero_add, show (1:ℂ)+w+1 = 2+w by ring] using
      rieszDenominator_inv_bound hs
  rw [characterRieszKernel_norm]
  calc
    _ = (‖characterContourSeries χ z f (1+w)‖*Real.exp (L*w.re)) *
        (1/(‖1+w‖*‖2+w‖)) := by ring
    _ ≤ (B*Real.exp (L*w.re))*(5/(1+w.im^2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le) hd
        (by positivity) (by positivity)
    _ = _ := by ring

theorem characterRieszKernel_left_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    {z L δ T B : ℝ} {f : ℂ → ℂ}
    (hδ : δ ≤ 1/2) (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hb : ∀ t ∈ Icc (-T) T,
      ‖characterContourSeries χ z f (1+(((-δ:ℝ):ℂ)+(t:ℂ)*I))‖ ≤ B) :
    ‖VIntegral (characterRieszKernel χ z L f) (-δ) (-T) T‖ ≤
      (5*B*Real.exp (-(L*δ)))*Real.pi := by
  apply verticalIntegral_bound_by_cauchy hT (by positivity)
  intro t ht
  have hs : 1/2 ≤ (1+(((-δ:ℝ):ℂ)+(t:ℂ)*I)).re := by simp <;> linarith
  have he := characterRieszKernel_point_bound χ (L := L) hB hs (hb t ⟨ht.1.le,ht.2⟩)
  simpa only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
    zero_mul, sub_zero, add_zero, add_im, mul_im, mul_one, zero_add, mul_neg] using he

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterContourEdges
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The horizontal edges of the regular character contour -/
namespace JointDickman
open Complex Set

theorem characterRieszKernel_horizontal_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    {z L δ c T B ε : ℝ} {f : ℂ → ℂ}
    (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1/2) (hc : 0 ≤ c) (hL : 0 ≤ L)
    (hB : 0 ≤ B) (hε : |ε| = 1)
    (hb : ∀ u ∈ Icc (-δ) c,
      ‖characterContourSeries χ z f (1+((u:ℂ)+((ε*T:ℝ):ℂ)*I))‖ ≤ B) :
    ‖HIntegral (characterRieszKernel χ z L f) (-δ) c (ε*T)‖ ≤
      (5*B*Real.exp (L*c)/(1+T^2))*(δ+c) := by
  have hac : -δ ≤ c := by linarith
  unfold HIntegral
  have hbound : ‖∫ u in -δ..c,
      characterRieszKernel χ z L f ((u:ℂ)+((ε*T:ℝ):ℂ)*I)‖ ≤
      (5*B*Real.exp (L*c)/(1+T^2))*|c-(-δ)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro u hu
    have hu' : -δ ≤ u ∧ u ≤ c := by
      have hh : u ∈ Ioc (-δ) c := by simpa only [uIoc_of_le hac] using hu
      exact ⟨hh.1.le,hh.2⟩
    have hre : (((u:ℂ)+((ε*T:ℝ):ℂ)*I)).re = u := by simp
    have him : (((u:ℂ)+((ε*T:ℝ):ℂ)*I)).im^2 = T^2 := by
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one,
        mul_zero, zero_add, add_zero]
      have heps : ε^2 = 1 := by nlinarith [sq_abs ε]
      rw [mul_pow, heps, one_mul]
    have hs : 1/2 ≤ (1+((u:ℂ)+((ε*T:ℝ):ℂ)*I)).re := by
      simp only [add_re, one_re, hre]
      linarith [hu'.1]
    have hp := characterRieszKernel_point_bound χ (L := L) hB hs (hb u hu')
    rw [hre, him] at hp
    apply hp.trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu'.2 hL)) (by positivity)
  rw [abs_of_nonneg (by linarith : 0 ≤ c-(-δ))] at hbound
  simpa only [sub_neg_eq_add, add_comm c δ] using hbound

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterContourShift
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A contour shift without a singular term for nonprincipal characters -/
namespace JointDickman
open Complex Set MeasureTheory

theorem characterRieszKernel_finite_shift {q : ℕ} (χ : DirichletCharacter ℂ q)
    {z L δ c T : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hδ : 0 < δ) (hδ4 : δ ≤ 1/4) (hc : 0 < c) (hc1 : c ≤ 1/2) (hT : 0 < T)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (zetaOpenRectangle δ (2*T))) :
    VIntegral (characterRieszKernel χ z L f) c (-T) T =
      VIntegral (characterRieszKernel χ z L f) (-δ/2) (-T) T +
      HIntegral (characterRieszKernel χ z L f) (-δ/2) c T -
      HIntegral (characterRieszKernel χ z L f) (-δ/2) c (-T) := by
  have has := characterContourSeries_analyticOnNhd χ hz hz1 hδ4 hf
  have hhol : DifferentiableOn ℂ (characterRieszKernel χ z L f)
      (Rectangle (-((δ/2:ℝ):ℂ)-(T:ℂ)*I) ((c:ℂ)+(T:ℂ)*I)) := by
    intro w hw
    have hrect := (mem_Rect (by simpa using (show -(δ/2) ≤ c by linarith))
      (by simpa using (show -T ≤ T by linarith)) w).mp hw
    have hre : -(δ/2) ≤ w.re ∧ w.re ≤ c := by simpa using And.intro hrect.1 hrect.2.1
    have him : -T ≤ w.im ∧ w.im ≤ T := by simpa using hrect.2.2
    have hmem : 1+w ∈ zetaOpenRectangle δ (2*T) := by
      change (1-δ < (1+w).re ∧ (1+w).re < 2) ∧
        (-(2*T) < (1+w).im ∧ (1+w).im < 2*T)
      simp only [add_re, one_re, add_im, one_im, zero_add]
      constructor <;> constructor <;> linarith [hre.1,hre.2,him.1,him.2]
    have hne1 : (1:ℂ)+w ≠ 0 := by
      intro he
      have hh := congrArg Complex.re he
      simp only [add_re, one_re, zero_re] at hh
      linarith [hre.1]
    have hne2 : (2:ℂ)+w ≠ 0 := by
      intro he
      have hh := congrArg Complex.re he
      norm_num at hh
      linarith [hre.1]
    have ha : AnalyticAt ℂ (fun v => characterContourSeries χ z f (1+v)) w :=
      (has (1+w) hmem).comp (analyticAt_const.add analyticAt_id)
    exact ((ha.mul ((analyticAt_const.mul analyticAt_id).cexp)).div
      ((analyticAt_const.add analyticAt_id).mul (analyticAt_const.add analyticAt_id))
      (mul_ne_zero hne1 hne2)).differentiableAt.differentiableWithinAt
  have he := HolomorphicOn.vanishesOnRectangle (U := Rectangle _ _) hhol subset_rfl
  simp only [RectangleIntegral, add_re, sub_re, neg_re, ofReal_re, ofReal_im,
    I_re, I_im, mul_re, mul_im, neg_zero, mul_zero, mul_one, zero_add,
    add_zero, sub_zero, zero_sub, add_im, sub_im, neg_im] at he
  simp only [neg_div] at he ⊢
  linear_combination he

theorem characterNormalizedPerron_finite_shift {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {z L δ c T : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hδ : 0 < δ) (hδ4 : δ ≤ 1/4) (hc : 0 < c) (hc1 : c ≤ 1/2) (hT : 0 < T)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (zetaOpenRectangle δ (2*T)))
    (hf0 : f (3/2) = primeCharacterLog χ (3/2))
    (he : ∀ s ∈ zetaOpenRectangle δ (2*T), exp (f s) = χ.LFunction s) :
    VIntegral (characterNormalizedPerron χ z L) c (-T) T =
      VIntegral (characterRieszKernel χ z L f) (-δ/2) (-T) T +
      HIntegral (characterRieszKernel χ z L f) (-δ/2) c T -
      HIntegral (characterRieszKernel χ z L f) (-δ/2) c (-T) := by
  rw [←characterRieszKernel_finite_shift χ hz hz1 hδ hδ4 hc hc1 hT hf]
  unfold VIntegral
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have htt : -T ≤ t ∧ t ≤ T := by
    simpa only [uIcc_of_le (by linarith : -T ≤ T), mem_Icc] using ht
  have hmem : 1+((c:ℂ)+(t:ℂ)*I) ∈ zetaOpenRectangle 0 (2*T) := by
    change (1-0 < (1+((c:ℂ)+(t:ℂ)*I)).re ∧ (1+((c:ℂ)+(t:ℂ)*I)).re < 2) ∧
      (-(2*T) < (1+((c:ℂ)+(t:ℂ)*I)).im ∧ (1+((c:ℂ)+(t:ℂ)*I)).im < 2*T)
    simp only [sub_zero, add_re, add_im, one_re, one_im, ofReal_re, ofReal_im,
      mul_re, mul_im, I_re, I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add]
    constructor <;> constructor <;> linarith [htt.1,htt.2]
  unfold characterNormalizedPerron characterRieszKernel
  dsimp only
  rw [characterContourSeries_eq_LSeries χ hz hz1 hδ (by linarith) hf hf0 he hmem]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterPerronBounds
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform decay on the original character Perron line -/
namespace JointDickman
open Complex

theorem characterLSeries_high_bound {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ s : ℂ, 1 < s.re → s.re ≤ 2 → 3 < |s.im| →
      ‖LSeries (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) s‖ ≤
        C*((q:ℝ)+2)^(1/4:ℝ)*|s.im|^(1/2:ℝ) := by
  obtain ⟨C,hC,hb⟩ := characterContourSeries_small_power hz hz1
    (by norm_num : (0:ℝ) < 1/4) (by norm_num : (1/4:ℝ) ≤ 1/4)
  refine ⟨C*3^(1/4:ℝ), by positivity, ?_⟩
  intro q _ χ hn s hs hs2 ht
  have ht0 : 0 < |s.im| := by linarith
  have hnS : ‖s‖+2 ≤ 3*|s.im| := by
    have hh := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_nonneg (by linarith : 0 ≤ s.re)] at hh
    linarith
  have hbase : ((q:ℝ)+2)*(‖s‖+2) ≤ 3*(((q:ℝ)+2)*|s.im|) := by
    nlinarith [mul_le_mul_of_nonneg_left hnS (show (0:ℝ) ≤ q+2 by positivity)]
  have hp : |s.im|^(1/4:ℝ) ≤ |s.im|^(1/2:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have h := hb q χ hn (primeCharacterLog χ) s (by linarith) (primeCharacterLog_exp χ hs)
  rw [characterContourSeries, ←squarefreeCharacterDirichletSeries_factorization χ hz hz1 hs] at h
  calc
    _ ≤ C*(((q:ℝ)+2)*(‖s‖+2))^(1/4:ℝ) := h
    _ ≤ C*(3*(((q:ℝ)+2)*|s.im|))^(1/4:ℝ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hbase (by norm_num)) hC.le
    _ = C*3^(1/4:ℝ)*((q:ℝ)+2)^(1/4:ℝ)*|s.im|^(1/4:ℝ) := by
      rw [Real.mul_rpow (by norm_num) (by positivity), Real.mul_rpow (by positivity) ht0.le]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)

theorem characterNormalizedPerron_norm {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z L : ℝ) (w : ℂ) :
    ‖characterNormalizedPerron χ z L w‖ =
      ‖LSeries (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) (1+w)‖ *
        Real.exp (L*w.re) / (‖1+w‖*‖2+w‖) := by
  simp only [characterNormalizedPerron, norm_div, norm_mul, Complex.norm_exp,
    mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]

theorem characterNormalizedPerron_high_bound {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ (L : ℝ) (w : ℂ), 0 < w.re → w.re ≤ 1 → 3 < |w.im| →
      ‖characterNormalizedPerron χ z L w‖ ≤
        C*((q:ℝ)+2)^(1/4:ℝ)*Real.exp (L*w.re)*|w.im|^(-3/2:ℝ) := by
  obtain ⟨C,hC,hb⟩ := characterLSeries_high_bound hz hz1
  refine ⟨C,hC,?_⟩
  intro q _ χ hn L w hw hw1 ht
  have ht0 : 0 < |w.im| := by linarith
  have hs := hb q χ hn (1+w) (by simpa using hw)
    (by simp only [add_re, one_re] <;> linarith) (by simpa using ht)
  simp only [add_im, one_im, zero_add] at hs
  have hd : |w.im|^2 ≤ ‖1+w‖*‖2+w‖ := by
    simpa only [add_im, one_im, zero_add, sq_abs,
      show (1:ℂ)+w+1 = 2+w by ring] using rieszDenominator_im_lower_bound (1+w)
  have hp : |w.im|^(1/2:ℝ)/|w.im|^2 = |w.im|^(-3/2:ℝ) := by
    rw [←Real.rpow_ofNat, ←Real.rpow_sub ht0]
    norm_num
  rw [characterNormalizedPerron_norm]
  calc
    _ ≤ (C*((q:ℝ)+2)^(1/4:ℝ)*|w.im|^(1/2:ℝ)*Real.exp (L*w.re))/|w.im|^2 :=
      div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hs (Real.exp_pos _).le)
        (pow_pos ht0 2) hd
    _ = C*((q:ℝ)+2)^(1/4:ℝ)*Real.exp (L*w.re)*
        (|w.im|^(1/2:ℝ)/|w.im|^2) := by ring
    _ = _ := by rw [hp]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterPerronIntegrable
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absolute integrability of the character Perron line -/
namespace JointDickman
open Complex MeasureTheory

 theorem squarefreeCharacterWeight_norm_le_one {q : ℕ} (χ : DirichletCharacter ℂ q)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (n : ℕ) :
    ‖(squarefreeWeight z n:ℂ)*χ (n:ZMod q)‖ ≤ 1 := by
  rw [norm_mul]
  apply (mul_le_of_le_one_right (norm_nonneg _) (χ.norm_le_one _)).trans
  simpa only [Complex.norm_real, Real.norm_eq_abs] using squarefreeWeight_abs_le_one_dup1 hz hz1 n

theorem characterLSeries_measurable {q : ℕ} (χ : DirichletCharacter ℂ q) (z : ℝ) :
    Measurable (LSeries (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q))) := by
  apply Measurable.tsum
  intro n
  apply Continuous.measurable
  exact continuous_iff_continuousAt.mpr (fun s => (LSeries.hasDerivAt_term _ n s).continuousAt)

theorem characterLSeries_vertical_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    {z σ : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (hσ : 1 < σ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ,
      ‖LSeries (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) ((σ:ℂ)+(t:ℂ)*I)‖ ≤ M := by
  have hs (t : ℝ) : LSeriesSummable
      (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) ((σ:ℂ)+(t:ℂ)*I) :=
    LSeriesSummable_of_bounded_of_one_lt_re
      (fun n _ => squarefreeCharacterWeight_norm_le_one χ hz hz1 n) (by simpa using hσ)
  let M := ∑' n, ‖LSeries.term (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q))
    ((σ:ℂ)+(0:ℂ)*I) n‖
  refine ⟨M,tsum_nonneg (fun _ => norm_nonneg _),fun t => ?_⟩
  calc
    _ ≤ ∑' n, ‖LSeries.term (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q))
        ((σ:ℂ)+(t:ℂ)*I) n‖ := norm_tsum_le_tsum_norm (hs t).norm
    _ = M := by
      apply tsum_congr
      intro n
      simp only [LSeries.norm_term_eq, add_re, ofReal_re, mul_re, ofReal_im,
        I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero]

theorem characterNormalizedPerron_integrable {q : ℕ} (χ : DirichletCharacter ℂ q)
    {z L c : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (hc : 0 < c) :
    Integrable (fun t : ℝ => characterNormalizedPerron χ z L ((c:ℂ)+(t:ℂ)*I)) := by
  obtain ⟨M,hM,hMb⟩ := characterLSeries_vertical_bound χ hz hz1 (show 1 < 1+c by linarith)
  have hm : Measurable (fun t : ℝ => characterNormalizedPerron χ z L ((c:ℂ)+(t:ℂ)*I)) := by
    unfold characterNormalizedPerron
    exact ((characterLSeries_measurable χ z).comp (by fun_prop)).mul (by fun_prop) |>.div (by fun_prop)
  have hi : Integrable (fun t : ℝ => (5*M*Real.exp (L*c))/(1+t^2)) := by
    simpa only [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul (5*M*Real.exp (L*c))
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards with t
  rw [characterNormalizedPerron_norm]
  have hseries : ‖LSeries (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q))
      (1+((c:ℂ)+(t:ℂ)*I))‖ ≤ M := by
    convert hMb t using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
    push_cast
    ring
  have hden := rieszDenominator_inv_bound (s := 1+((c:ℂ)+(t:ℂ)*I)) (by simp <;> linarith)
  have hden' : 1/(‖1+((c:ℂ)+(t:ℂ)*I)‖*‖2+((c:ℂ)+(t:ℂ)*I)‖) ≤ 5/(1+t^2) := by
    simpa only [show (1:ℂ)+((c:ℂ)+(t:ℂ)*I)+1 = 2+((c:ℂ)+(t:ℂ)*I) by ring,
      add_im, one_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero,
      zero_add, add_zero] using hden
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero]
  calc
    _ ≤ (M*Real.exp (L*c))*(5/(1+t^2)) := by
      rw [div_eq_mul_inv]
      apply mul_le_mul (mul_le_mul_of_nonneg_right hseries (Real.exp_pos _).le)
        _ (by positivity) (by positivity)
      simpa only [one_div] using hden'
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterPerronTails
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Tails of the character Perron integral -/
namespace JointDickman
open Complex MeasureTheory Set

theorem characterNormalizedPerron_tail_bound {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ L c T ε : ℝ, 0 < c → c ≤ 1 → 3 < T → |ε| = 1 →
      ‖∫ t : ℝ in Ioi T, characterNormalizedPerron χ z L ((c:ℂ)+((ε*t:ℝ):ℂ)*I)‖ ≤
        2*C*((q:ℝ)+2)^(1/4:ℝ)*Real.exp (L*c)*T^(-1/2:ℝ) := by
  obtain ⟨C,hC,hb⟩ := characterNormalizedPerron_high_bound hz hz1
  refine ⟨C,hC,?_⟩
  intro q _ χ hn L c T ε hc hc1 hT hε
  have hT0 : 0 < T := by linarith
  have hi : IntegrableOn (fun t : ℝ =>
      C*((q:ℝ)+2)^(1/4:ℝ)*Real.exp (L*c)*t^(-3/2:ℝ)) (Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3/2:ℝ) < -1) hT0).const_mul _
  calc
    _ ≤ ∫ t : ℝ in Ioi T, C*((q:ℝ)+2)^(1/4:ℝ)*Real.exp (L*c)*t^(-3/2:ℝ) := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := hT0.trans ht
      have hp := hb q χ hn L ((c:ℂ)+((ε*t:ℝ):ℂ)*I)
        (by simpa using hc) (by simpa using hc1)
        (by simpa only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one,
          mul_zero, zero_add, add_zero, abs_mul, hε, one_mul, abs_of_pos ht0] using hT.trans ht)
      simpa only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
        zero_mul, sub_zero, add_zero, add_im, mul_im, mul_one, zero_add,
        abs_mul, hε, one_mul, abs_of_pos ht0] using hp
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-3/2:ℝ) < -1) hT0]
      norm_num
      ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreePerronTruncation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative truncation of the normalized squarefree Perron line -/
namespace JointDickman
open Complex MeasureTheory Set

theorem perron_normalization_norm :
    ‖(1/(2*(Real.pi:ℂ)*I):ℂ)‖ = 1/(2*Real.pi) := by
  simp [Real.norm_eq_abs,abs_of_pos Real.pi_pos]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterPerronTruncation
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative truncation of the character Perron line -/
namespace JointDickman
open Complex MeasureTheory Set

theorem characterNormalizedPerron_truncation_bound {z : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ L c T : ℝ, 0 < c → c ≤ 1 → 3 < T →
      ‖VerticalIntegral' (characterNormalizedPerron χ z L) c -
        (1/(2*(Real.pi:ℂ)*I))*VIntegral (characterNormalizedPerron χ z L) c (-T) T‖ ≤
        C*((q:ℝ)+2)^(1/4:ℝ)*Real.exp (L*c)*T^(-1/2:ℝ) := by
  obtain ⟨C,hC,hb⟩ := characterNormalizedPerron_tail_bound hz hz1
  refine ⟨4*C/(2*Real.pi), by positivity, ?_⟩
  intro q _ χ hn L c T hc hc1 hT
  let P := characterNormalizedPerron χ z L
  have hlo : ‖∫ t : ℝ in Iic (-T), P ((c:ℂ)+(t:ℂ)*I)‖ ≤
      2*C*((q:ℝ)+2)^(1/4:ℝ)*Real.exp (L*c)*T^(-1/2:ℝ) := by
    rw [←integral_comp_neg_Ioi T (fun t : ℝ => P ((c:ℂ)+(t:ℂ)*I))]
    simpa only [neg_one_mul] using hb q χ hn L c T (-1) hc hc1 hT (by norm_num)
  have hhi : ‖∫ t : ℝ in Ici T, P ((c:ℂ)+(t:ℂ)*I)‖ ≤
      2*C*((q:ℝ)+2)^(1/4:ℝ)*Real.exp (L*c)*T^(-1/2:ℝ) := by
    rw [integral_Ici_eq_integral_Ioi]
    simpa only [one_mul] using hb q χ hn L c T 1 hc hc1 hT (by norm_num)
  have heq : VerticalIntegral' P c -
      (1/(2*(Real.pi:ℂ)*I))*VIntegral P c (-T) T =
      (1/(2*(Real.pi:ℂ)*I))*I*
        ((∫ t : ℝ in Iic (-T), P ((c:ℂ)+(t:ℂ)*I)) +
         (∫ t : ℝ in Ici T, P ((c:ℂ)+(t:ℂ)*I))) := by
    rw [VerticalIntegral', verticalIntegral_split_three (-T) T
      (characterNormalizedPerron_integrable χ hz hz1 hc)]
    simp only [smul_eq_mul]
    ring
  rw [heq, norm_mul, norm_mul, perron_normalization_norm, norm_I, mul_one]
  calc
    _ ≤ (1/(2*Real.pi))*(
      ‖∫ t : ℝ in Iic (-T), P ((c:ℂ)+(t:ℂ)*I)‖ +
      ‖∫ t : ℝ in Ici T, P ((c:ℂ)+(t:ℂ)*I)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ ≤ (1/(2*Real.pi))*(2*C*((q:ℝ)+2)^(1/4:ℝ)*Real.exp (L*c)*T^(-1/2:ℝ) +
        2*C*((q:ℝ)+2)^(1/4:ℝ)*Real.exp (L*c)*T^(-1/2:ℝ)) :=
      mul_le_mul_of_nonneg_left (add_le_add hlo hhi) (by positivity)
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterContourEstimate
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Combining the character contour errors -/
namespace JointDickman
open Complex Set

theorem characterPerron_contour_bound {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ L δ c T B : ℝ, 0 ≤ L → 0 < δ → δ ≤ 1/4 → 0 < c → c ≤ 1/2 → 3 < T → 0 ≤ B →
      ∀ f : ℂ → ℂ, AnalyticOnNhd ℂ f (zetaOpenRectangle δ (2*T)) →
      f (3/2) = primeCharacterLog χ (3/2) →
      (∀ s ∈ zetaOpenRectangle δ (2*T), exp (f s) = χ.LFunction s) →
      (∀ t ∈ Icc (-T) T,
        ‖characterContourSeries χ z f (1+(((-δ/2:ℝ):ℂ)+(t:ℂ)*I))‖ ≤ B) →
      (∀ u ∈ Icc (-δ/2) c,
        ‖characterContourSeries χ z f (1+((u:ℂ)+(T:ℂ)*I))‖ ≤ B) →
      (∀ u ∈ Icc (-δ/2) c,
        ‖characterContourSeries χ z f (1+((u:ℂ)-(T:ℂ)*I))‖ ≤ B) →
      ‖VerticalIntegral' (characterNormalizedPerron χ z L) c‖ ≤
        C*((q:ℝ)+2)^(1/4:ℝ)*Real.exp (L*c)*T^(-1/2:ℝ) +
        (1/(2*Real.pi))*((5*B*Real.exp (-(L*(δ/2))))*Real.pi +
          2*((5*B*Real.exp (L*c)/(1+T^2))*(δ/2+c))) := by
  obtain ⟨C,hC,htr⟩ := characterNormalizedPerron_truncation_bound hz hz1
  refine ⟨C,hC,?_⟩
  intro q _ χ hn L δ c T B hL hδ hδ4 hc hc1 hT hB f hf hf0 he hl hu hd
  have hleft := characterRieszKernel_left_bound χ (z := z) (f := f) (L := L) (δ := δ/2) (T := T) (B := B)
    (by linarith) (by linarith) hB (by simpa only [neg_div] using hl)
  have hup := characterRieszKernel_horizontal_bound χ (z := z) (f := f) (L := L) (δ := δ/2) (T := T) (B := B)
    (ε := 1) (by linarith) (by linarith) hc.le hL hB (by norm_num)
    (by simpa only [one_mul, neg_div] using hu)
  have hdown := characterRieszKernel_horizontal_bound χ (z := z) (f := f) (L := L) (δ := δ/2) (T := T) (B := B)
    (ε := -1) (by linarith) (by linarith) hc.le hL hB (by norm_num)
    (by simpa only [neg_one_mul, one_mul, ofReal_neg, neg_mul, ←sub_eq_add_neg, neg_div] using hd)
  have hs := characterNormalizedPerron_finite_shift χ (L := L) hz hz1 hδ hδ4 hc hc1 (by linarith) hf hf0 he
  have hnorm : ‖(1/(2*(Real.pi:ℂ)*I))*VIntegral (characterNormalizedPerron χ z L) c (-T) T‖ ≤
      (1/(2*Real.pi))*((5*B*Real.exp (-(L*(δ/2))))*Real.pi +
        2*((5*B*Real.exp (L*c)/(1+T^2))*(δ/2+c))) := by
    rw [hs, norm_mul, perron_normalization_norm]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hh := (norm_sub_le
      (VIntegral (characterRieszKernel χ z L f) (-δ/2) (-T) T +
        HIntegral (characterRieszKernel χ z L f) (-δ/2) c T)
      (HIntegral (characterRieszKernel χ z L f) (-δ/2) c (-T))).trans
        (add_le_add (norm_add_le _ _) le_rfl)
    have hp : ‖HIntegral (characterRieszKernel χ z L f) (-δ/2) c T‖ ≤
        (5*B*Real.exp (L*c)/(1+T^2))*(δ/2+c) := by simpa only [one_mul, neg_div] using hup
    have hm : ‖HIntegral (characterRieszKernel χ z L f) (-δ/2) c (-T)‖ ≤
        (5*B*Real.exp (L*c)/(1+T^2))*(δ/2+c) := by simpa only [neg_one_mul, neg_div] using hdown
    have hj : ‖VIntegral (characterRieszKernel χ z L f) (-δ/2) (-T) T‖ ≤
        (5*B*Real.exp (-(L*(δ/2))))*Real.pi := by simpa only [neg_div] using hleft
    linarith
  have htriangle := norm_add_le
    (VerticalIntegral' (characterNormalizedPerron χ z L) c -
      (1/(2*(Real.pi:ℂ)*I))*VIntegral (characterNormalizedPerron χ z L) c (-T) T)
    ((1/(2*(Real.pi:ℂ)*I))*VIntegral (characterNormalizedPerron χ z L) c (-T) T)
  rw [sub_add_cancel] at htriangle
  exact htriangle.trans (add_le_add (htr q χ hn L c T hc (by linarith) hT) hnorm)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterRectangleBound
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single uniform majorant for all three shifted contour edges -/
namespace JointDickman
open Complex Set

theorem characterContourSeries_closed_rectangle_bound {z η : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1/4) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ δ c T : ℝ, 0 < δ → δ ≤ η → c ≤ 1/2 → 0 < T →
      ∀ f : ℂ → ℂ,
      (∀ s ∈ zetaOpenRectangle δ (2*T), exp (f s) = χ.LFunction s) →
      ∀ w : ℂ, -δ/2 ≤ w.re → w.re ≤ c → |w.im| ≤ T →
      ‖characterContourSeries χ z f (1+w)‖ ≤ C*(((q:ℝ)+2)*(T+2))^η := by
  obtain ⟨C,hC,hb⟩ := characterContourSeries_rectangle_bound hz hz1 hη hη1
  refine ⟨C,hC,?_⟩
  intro q _ χ hn δ c T hδ hδη hc hT f he w hw hwc hwi
  have hmem : 1+w ∈ zetaOpenRectangle δ (2*T) := by
    change (1-δ < (1+w).re ∧ (1+w).re < 2) ∧
      (-(2*T) < (1+w).im ∧ (1+w).im < 2*T)
    simp only [add_re, one_re, add_im, one_im, zero_add]
    obtain ⟨hwmin,hwmax⟩ := abs_le.mp hwi
    constructor <;> constructor <;> linarith
  apply hb q χ hn f T hT.le (1+w) _ _ _ (he (1+w) hmem)
  · simp only [add_re, one_re]
    linarith
  · simp only [add_re, one_re]
    linarith
  · simpa only [add_im, one_im, zero_add] using hwi

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterPerronEstimate
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An unconditional quantitative bound for the actual character Perron integral -/
namespace JointDickman
open Complex Set

theorem characterPerron_estimate_jd_oai {z ε : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ A C K : ℝ, 0 < A ∧ A ≤ 1/4 ∧ 0 < C ∧ 0 < K ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ L c T : ℝ, 0 ≤ L → 0 < c → c ≤ 1/2 → 3 < T →
      let δ := characterContourWidth A ε q (2*T)
      let B := K*(((q:ℝ)+2)*(T+2))^(1/4:ℝ)
      ‖VerticalIntegral' (characterNormalizedPerron χ z L) c‖ ≤
        C*((q:ℝ)+2)^(1/4:ℝ)*Real.exp (L*c)*T^(-1/2:ℝ) +
        (1/(2*Real.pi))*((5*B*Real.exp (-(L*(δ/2))))*Real.pi +
          2*((5*B*Real.exp (L*c)/(1+T^2))*(δ/2+c))) := by
  obtain ⟨A,hA,hA4,hlog⟩ := character_rectangle_log hε hε1
  obtain ⟨C,hC,hest⟩ := characterPerron_contour_bound hz hz1
  obtain ⟨K,hK,hbounds⟩ := characterContourSeries_closed_rectangle_bound hz hz1
    (by norm_num : (0:ℝ) < 1/4) (by norm_num : (1/4:ℝ) ≤ 1/4)
  refine ⟨A,C,K,hA,hA4,hC,hK,?_⟩
  intro q _ χ hn L c T hL hc hc1 hT
  let δ := characterContourWidth A ε q (2*T)
  let B := K*(((q:ℝ)+2)*(T+2))^(1/4:ℝ)
  have hδ : 0 < δ := by
    dsimp [δ, characterContourWidth]
    exact mul_pos hA (Real.rpow_pos_of_pos (by positivity) _)
  have hδ4 : δ ≤ 1/4 := by
    have hw : 1 ≤ ((q:ℝ)+2)*(2*T+2) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) q]
    have hp := Real.rpow_le_one_of_one_le_of_nonpos hw (show -ε ≤ 0 by linarith)
    exact (mul_le_of_le_one_right hA.le hp).trans hA4
  obtain ⟨f,hf,hf0,he⟩ := hlog q χ hn (2*T) (by linarith)
    (primeCharacterLog χ (3/2)) (primeCharacterLog_exp χ (by norm_num))
  have hb (w : ℂ) (hw : -δ/2 ≤ w.re) (hwc : w.re ≤ c) (hwi : |w.im| ≤ T) :
      ‖characterContourSeries χ z f (1+w)‖ ≤ B :=
    hbounds q χ hn δ c T hδ hδ4 hc1 (by linarith) f he w hw hwc hwi
  apply hest q χ hn L δ c T B hL hδ hδ4 hc hc1 hT (by dsimp [B] <;> positivity) f hf hf0 he
  · intro t ht
    apply hb
    · simp
    · simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
        zero_mul, sub_zero, add_zero]
      linarith
    · simpa only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero,
        mul_one, zero_add, add_zero] using abs_le.mpr ht
  · intro u hu
    apply hb
    · simpa using hu.1
    · simpa using hu.2
    · simp [abs_of_pos (show 0 < T by linarith)]
  · intro u hu
    have hw : |((u:ℂ)-(T:ℂ)*I).im| ≤ T := by
      simp [abs_of_pos (show 0 < T by linarith)]
    have hh := hb ((u:ℂ)-(T:ℂ)*I) (by simpa using hu.1) (by simpa using hu.2) hw
    simpa only [sub_eq_add_neg] using hh

end JointDickman

end OAI
end

theorem solution : type_of% @OAI.JointDickman.characterPerron_estimate_jd_oai := @OAI.JointDickman.characterPerron_estimate_jd_oai
