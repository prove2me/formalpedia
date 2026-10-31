-- Prove2me | solution 1 for OAI.Ostmann.twoInfiniteSummandsImpossible
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:53:02.548373+00:00
-- url     : https://prove2.me/submissions/ce76ac72-513f-4ef0-bb59-74dfa079abcf

import Mathlib
import Definitions.Def_OstmannComplete
import Definitions.Def_OAIQ095D003
import Theorems.Thm_OAI_Ostmann_publishedComplexZeroDensity
import Theorems.Thm_OAI_Ostmann_publishedQuadraticLargeSieve
import Theorems.Thm_OAI_Ostmann_twoInfiniteSummandsImpossible_without_summand_size

section
-- module Solutions.OAIQ095_OS.PrimeGaps_DirichletGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
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
  have hp : (-(s+1)).re < -1 := by simp only [neg_re,add_re,one_re]; linarith
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
  have hs0 : s-1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
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
  have hB : 1 ≤ B := by dsimp [B]; nlinarith [norm_nonneg s]
  let N := ⌈B⌉₊
  have hBN : B ≤ (N:ℝ) := Nat.le_ceil B
  have hN : 1 ≤ N := by exact_mod_cast (hB.trans hBN)
  have hN2 : (N:ℝ) ≤ 2*B := by
    have := Nat.ceil_lt_add_one (zero_lt_one.trans_le hB).le
    change (N:ℝ) < B+1 at this
    linarith
  have hcut := regularSeries_norm_cutoff hf0 hf hc hD hb hε hε1 hN hs
    (show D*(1+‖s‖) ≤ (N:ℝ) from (by dsimp [B] at hBN; nlinarith [norm_nonneg s]))
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
-- module Solutions.OAIQ095_OS.PrimeGaps_TaylorBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
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
    have he : ((2-z:ℝ):ℂ)-(2:ℂ) = -(z:ℂ) := by push_cast; ring
    simpa [he,Complex.norm_real,Real.norm_eq_abs] using hz
  have hs := (Complex.hasSum_taylorSeries_on_ball hf hmem).map Complex.reCLM Complex.continuous_re
  change HasSum (fun n => ((n.factorial:ℂ)⁻¹ *
    ((((2-z:ℝ):ℂ)-2)^n * iteratedDeriv n H 2)).re) (H ((2-z:ℝ):ℂ)).re at hs
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  dsimp [signedTaylorCoeff]
  have he : ((2-z:ℝ):ℂ)-(2:ℂ) = -(z:ℂ) := by push_cast; ring
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
-- module Solutions.OAIQ095_OS.PrimeGaps_SiegelBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
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
    have hβne : (β:ℂ)≠1 := by intro h; have := congrArg Complex.re h; simp at this; linarith
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
  have hβne : (β:ℂ)≠1 := by intro h; have := congrArg Complex.re h; simp at this; linarith
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
  have hβ₀ : 99/100≤β₀ := by dsimp [β₀]; linarith
  have hβ₀1 : β₀<1 := by dsimp [β₀]; linarith
  by_cases hex : ∃ r : ℕ, ∃ ψ : DirichletCharacter ℂ (r+1),
      ψ.IsPrimitive ∧ ψ≠1 ∧ ψ^2=1 ∧ ∃ β ∈ Set.Icc β₀ 1, ψ.LFunction β=0
  · obtain ⟨r,ψ,hψprim,hψ,hψ2,β,hβI,hzero⟩ := hex
    have hβ1 : β<1 := lt_of_le_of_ne hβI.2 (by
      intro he
      apply DirichletCharacter.LFunction_apply_one_ne_zero hψ
      simpa [he] using hzero)
    have hβ : 99/100≤β := hβ₀.trans hβI.1
    have hβε : 60*(1-β)≤ε/2 := by dsimp [β₀] at hβI; linarith [hβI.1]
    obtain ⟨K,hK,hgrowth⟩ := LFunction_norm_small_power (by linarith : 0<ε/4)
      (by linarith : ε/4≤1/2)
    let D : ℝ := 3*((r:ℝ)+3)
    let U : ℝ := ‖ψ.LFunction 1‖*K*D^(ε/2)
    have hD : 0<D := by dsimp [D]; positivity
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
    have hb := hgrowth ((r+1)*q) (productCharacter ψ χ) hp 1 (by simp; linarith)
    have hQ0 : 0<(q:ℝ)+1 := by positivity
    have he : 2*(ε/4)=ε/2 := by ring
    rw [he] at hb
    have hbase : (((r+1)*q:ℕ):ℝ)+2≤((r:ℝ)+3)*((q:ℝ)+1) := by push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) q,Nat.cast_nonneg (α:=ℝ) r]
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
        _ = _ := by dsimp [U]; ring
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
      (by dsimp [β₀]; linarith) hqbig
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
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterSiegelTools
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bridges from the proved Siegel value bound to actual real zeros

The three reused character-analysis modules are the unchanged completed result
028 sources at f5371230bbb5024338caeeb3a6eaf46fb2cd4842. The derivative bridge
below specializes their regular Dirichlet-series bound near the line Re(s)=1.
-/

namespace Ostmann

open Filter Topology Complex

 theorem real_character_quadratic {q : ℕ} [NeZero q] (χ : DirichletCharacter ℝ q) :
    χ.IsQuadratic := by
  intro x
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    have hh := χ.unit_norm_eq_one u
    rw [Real.norm_eq_abs] at hh
    rcases abs_eq_abs.mp (hh.trans (abs_one.symm)) with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · exact Or.inl (χ.map_nonunit hx)

 theorem character_deriv_small_power {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ s : ℂ, 1 - η / 2 ≤ s.re →
      ‖deriv χ.LFunction s‖ ≤ K * (((q : ℝ) + 2) * (‖s‖ + 2)) ^ (2 * η) := by
  obtain ⟨K, hK, h⟩ := LargePrimeGaps.regularSeries_deriv_norm_small_power hη hη1
  refine ⟨K, hK, ?_⟩
  intro q _ χ hχ s hs
  have he : LargePrimeGaps.regularSeries
      (LargePrimeGaps.positiveCoefficients (fun n => χ (n : ZMod q))) 0 =ᶠ[𝓝 s] χ.LFunction := by
    filter_upwards [(continuous_re.tendsto s).eventually
      (lt_mem_nhds (by linarith : 0 < s.re))] with z hz
    exact LargePrimeGaps.regularSeries_character_eq hχ hz
  rw [← he.deriv_eq]
  have hb := h _ 0 (q + 1) (LargePrimeGaps.positiveCoefficients_zero _)
    (LargePrimeGaps.positiveCoefficients_norm_le (fun n => χ.norm_le_one _))
    (by simp) (by positivity) (fun t _ => LargePrimeGaps.discrepancy_character_bound hχ t) s hs
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  congr 3
  ring

 theorem character_zero_value_bound {η K : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 2)
    (hK : 0 < K) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hd : ∀ s : ℂ, 1 - η / 2 ≤ s.re →
      ‖deriv χ.LFunction s‖ ≤ K * (((q : ℝ) + 2) * (‖s‖ + 2)) ^ (2 * η))
    {β : ℝ} (hβ : 1 - η / 2 ≤ β) (hβ1 : β < 1) (hz : χ.LFunction (β : ℂ) = 0) :
    ‖χ.LFunction 1‖ ≤ (1 - β) * (K * 4 ^ (2 * η) * ((q : ℝ) + 2) ^ (2 * η)) := by
  have hbnd : ∀ s ∈ Metric.closedBall (1 : ℂ) (η / 2),
      ‖deriv χ.LFunction s‖ ≤ K * 4 ^ (2 * η) * ((q : ℝ) + 2) ^ (2 * η) := by
    intro s hs
    have hsD := Metric.mem_closedBall.mp hs
    have hsR : 1 - η / 2 ≤ s.re := by
      have hh := Complex.re_le_norm (1 - s)
      rw [Complex.sub_re, Complex.one_re, ← dist_eq_norm, dist_comm] at hh
      linarith
    have hsN : ‖s‖ ≤ 2 := by
      have hh : ‖s‖ ≤ dist s 1 + 1 := by simpa only [norm_one, sub_add_cancel, dist_eq_norm] using norm_add_le (s - 1) (1 : ℂ)
      linarith
    calc
      _ ≤ K * (((q : ℝ) + 2) * (‖s‖ + 2)) ^ (2 * η) := hd s hsR
      _ ≤ K * (((q : ℝ) + 2) * 4) ^ (2 * η) := by gcongr; nlinarith
      _ = _ := by rw [Real.mul_rpow (by positivity) (by norm_num)]; ring
  have hbetaMem : (β : ℂ) ∈ Metric.closedBall (1 : ℂ) (η / 2) := by
    rw [Metric.mem_closedBall, dist_eq_norm, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith : β - 1 < 0)]
    linarith
  have honeMem : (1 : ℂ) ∈ Metric.closedBall (1 : ℂ) (η / 2) := by
    simp only [Metric.mem_closedBall, dist_self]
    positivity
  have hh := (convex_closedBall (1 : ℂ) (η / 2)).norm_image_sub_le_of_norm_deriv_le
    (fun s _ => (DirichletCharacter.differentiable_LFunction hχ s)) hbnd hbetaMem honeMem
  rw [hz, sub_zero] at hh
  have hnorm : ‖(1 : ℂ) - (β : ℂ)‖ = 1 - β := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : 0 < 1 - β)]
  rw [hnorm] at hh
  nlinarith [hh]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SiegelBoundProof
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Siegel's bound for the actual primitive real zeros

The proved quadratic L-value estimate is combined with a small-power bound
for the derivative in a fixed strip. Constants may depend on the exponent.
-/

namespace Ostmann

open Complex

 theorem publishedSiegelBound : PublishedSiegelBound := by
  intro ε hε
  let η : ℝ := min (ε / 4) (1 / 4)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hη4 : η ≤ 1 / 4 := min_le_right _ _
  have hηε : 3 * η ≤ ε := by have := min_le_left (ε / 4) (1 / 4); dsimp [η]; linarith
  obtain ⟨c, hc, hL⟩ := LargePrimeGaps.quadratic_siegel hη (by linarith : η ≤ 1)
  obtain ⟨K, hK, hd⟩ := character_deriv_small_power hη (by linarith : η ≤ 1 / 2)
  let D : ℝ := K * 4 ^ (2 * η)
  let C : ℝ := max (D * 3 ^ ε / c) (2 / η)
  have hD : 0 < D := mul_pos hK (Real.rpow_pos_of_pos (by norm_num) _)
  have hC : 0 < C := lt_max_of_lt_right (by positivity)
  refine ⟨C, hC, ?_⟩
  intro e
  let : NeZero e.modulus := ⟨e.positive.ne'⟩
  have hq : (1 : ℝ) ≤ e.modulus := by exact_mod_cast e.positive
  have hqpow : 1 ≤ (e.modulus : ℝ) ^ ε := Real.one_le_rpow hq hε.le
  have hgap : 0 < 1 - e.beta := sub_pos.mpr e.beta_lt_one
  by_cases hnear : 1 - η / 2 ≤ e.beta
  · let rc : PrimitiveRealCharacter := ⟨e.modulus, e.positive, e.character, e.primitive, e.nontrivial⟩
    let χ := rc.complexCharacter
    have hχ : χ ≠ 1 := rc.asComplex.nontrivial
    have hχprim : χ.IsPrimitive := rc.asComplex.primitive
    have hχquad : χ ^ 2 = 1 :=
      ((real_character_quadratic e.character).comp Complex.ofRealHom).sq_eq_one
    have hlow := hL e.modulus χ hχprim hχ hχquad
    have hzero : χ.LFunction (e.beta : ℂ) = 0 := e.zero
    have hu := character_zero_value_bound hη (by linarith) hK e.modulus χ hχ
      (hd e.modulus χ hχ) hnear e.beta_lt_one hzero
    let R : ℝ := e.modulus + 2
    have hR : 0 < R := by dsimp [R]; positivity
    have hR1 : 1 ≤ R := by dsimp [R]; linarith
    have hlowR : c * R ^ (-η) ≤ ‖χ.LFunction 1‖ := by
      apply le_trans ?_ hlow
      apply mul_le_mul_of_nonneg_left ?_ hc.le
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (by dsimp [R]; linarith) (by linarith)
    have hm := mul_le_mul_of_nonneg_right (hlowR.trans hu) (Real.rpow_nonneg hR.le η)
    have he : R ^ (-η) * R ^ η = 1 := by rw [← Real.rpow_add hR]; simp
    have huR : c ≤ (1 - e.beta) * D * R ^ (3 * η) := by
      have hr : R ^ (2 * η) * R ^ η = R ^ (3 * η) := by
        rw [← Real.rpow_add hR]
        congr 1
        ring
      calc
        c = c * R ^ (-η) * R ^ η := by rw [mul_assoc c, he, mul_one]
        _ ≤ (1 - e.beta) * (D * R ^ (2 * η)) * R ^ η := hm
        _ = (1 - e.beta) * D * (R ^ (2 * η) * R ^ η) := by ring
        _ = _ := by rw [hr]
    have hpow : R ^ (3 * η) ≤ 3 ^ ε * (e.modulus : ℝ) ^ ε := by
      calc
        _ ≤ R ^ ε := Real.rpow_le_rpow_of_exponent_le hR1 hηε
        _ ≤ (3 * (e.modulus : ℝ)) ^ ε :=
          Real.rpow_le_rpow hR.le (by dsimp [R]; linarith) hε.le
        _ = _ := Real.mul_rpow (by norm_num) (by positivity)
    have hraw : c ≤ (1 - e.beta) * D * (3 ^ ε * (e.modulus : ℝ) ^ ε) :=
      huR.trans (mul_le_mul_of_nonneg_left hpow (mul_nonneg hgap.le hD.le))
    have hone : 1 ≤ (D * 3 ^ ε / c * (e.modulus : ℝ) ^ ε) * (1 - e.beta) := by
      calc
        1 = c / c := (div_self hc.ne').symm
        _ ≤ ((1 - e.beta) * D * (3 ^ ε * (e.modulus : ℝ) ^ ε)) / c :=
          div_le_div_of_nonneg_right hraw hc.le
        _ = _ := by ring
    have hbound : (1 - e.beta)⁻¹ ≤ D * 3 ^ ε / c * (e.modulus : ℝ) ^ ε := by
      rw [← one_div]
      exact (div_le_iff₀ hgap).mpr hone
    exact hbound.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have hfar : (1 - e.beta)⁻¹ ≤ 2 / η := by
      have hh := one_div_le_one_div_of_le (by positivity : 0 < η / 2)
        (show η / 2 ≤ 1 - e.beta by linarith)
      simpa only [one_div, inv_div] using hh
    exact hfar.trans ((le_max_right _ _).trans (le_mul_of_one_le_right hC.le hqpow))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_MainWithoutSiegel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Both main theorems after proving the actual Siegel zero bound -/

namespace Ostmann

theorem twoInfiniteSummandsImpossible_without_siegel
    (sieve : PublishedQuadraticLargeSieve)
    (hD : PublishedComplexZeroDensity actualCharacterZeros) :
    TwoInfiniteSummandsImpossible :=
  twoInfiniteSummandsImpossible_without_summand_size publishedSiegelBound sieve hD

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_MainWithoutQuadraticSieve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Both main theorems after proving the quadratic large sieve -/

namespace Ostmann

theorem twoInfiniteSummandsImpossible_without_quadratic_sieve
    (hD : PublishedComplexZeroDensity actualCharacterZeros) :
    TwoInfiniteSummandsImpossible :=
  twoInfiniteSummandsImpossible_without_siegel publishedQuadraticLargeSieve hD

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ostmann's inverse Goldbach theorems

The quadratic large sieve and the exact character-zero density estimate give
both the two-infinite-summands contradiction and asymptotic indecomposability.
-/

namespace Ostmann

/-- Theorem 2.3: two infinite nonnegative summands cannot give the primes
outside a finite initial interval. -/
theorem twoInfiniteSummandsImpossible_oai : TwoInfiniteSummandsImpossible :=
  twoInfiniteSummandsImpossible_without_quadratic_sieve publishedComplexZeroDensity

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.twoInfiniteSummandsImpossible_oai := @OAI.Ostmann.twoInfiniteSummandsImpossible_oai
