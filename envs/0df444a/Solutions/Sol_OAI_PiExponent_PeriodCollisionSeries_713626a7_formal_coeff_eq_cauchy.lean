-- Prove2me | solution 1 for OAI.PiExponent.PeriodCollisionSeries_713626a7.formal_coeff_eq_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T19:09:57.603794+00:00
-- url     : https://prove2.me/submissions/2d818d94-9b49-4833-a292-e9ec4cc2684c

import Definitions.Def_PiExponent_PeriodCollisionSeries_713626a7
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Analytic.Uniqueness

open OAI.PiExponent
open OAI.PiExponent.FiniteMinorAnalysis_690acb6f
open OAI.PiExponent.PeriodCollisionSeries_713626a7
open Filter Topology
open scoped BigOperators

namespace S45PM

/-- `F` represents `g` on the open unit disc, with absolute convergence. -/
def Rep (F : PowerSeries ℂ) (g : ℂ → ℂ) : Prop :=
  ∀ t : ℂ, ‖t‖ < 1 → Summable (fun n => ‖PowerSeries.coeff n F * t ^ n‖) ∧
    HasSum (fun n => PowerSeries.coeff n F * t ^ n) (g t)

lemma rep_congr {F : PowerSeries ℂ} {g g' : ℂ → ℂ} (h : Rep F g)
    (e : ∀ t : ℂ, ‖t‖ < 1 → g t = g' t) : Rep F g' := fun t ht =>
  ⟨(h t ht).1, e t ht ▸ (h t ht).2⟩

lemma rep_C (c : ℂ) : Rep (PowerSeries.C c) (fun _ => c) := by
  intro t _
  have e : (fun n => PowerSeries.coeff n (PowerSeries.C c) * t ^ n) =
      fun n => if n = 0 then c else 0 := by
    funext n; rw [PowerSeries.coeff_C]; split_ifs with h <;> simp [h]
  refine ⟨?_, e ▸ hasSum_ite_eq 0 c⟩
  apply summable_of_ne_finset_zero (s := {0})
  intro n hn; simp at hn; simp [PowerSeries.coeff_C, hn]

lemma rep_X : Rep PowerSeries.X (fun t => t) := by
  intro t _
  have e : (fun n => PowerSeries.coeff n (PowerSeries.X : PowerSeries ℂ) * t ^ n) =
      fun n => if n = 1 then t else 0 := by
    funext n; rw [PowerSeries.coeff_X]; split_ifs with h <;> simp [h]
  refine ⟨?_, e ▸ hasSum_ite_eq 1 t⟩
  apply summable_of_ne_finset_zero (s := {1})
  intro n hn; simp at hn; simp [PowerSeries.coeff_X, hn]

lemma rep_add {F G : PowerSeries ℂ} {f g : ℂ → ℂ} (hF : Rep F f) (hG : Rep G g) :
    Rep (F + G) (fun t => f t + g t) := by
  intro t ht
  obtain ⟨s1, h1⟩ := hF t ht
  obtain ⟨s2, h2⟩ := hG t ht
  refine ⟨?_, ?_⟩
  · refine (s1.add s2).of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    rw [map_add, add_mul]; exact norm_add_le _ _
  · simpa [add_mul] using h1.add h2

lemma rep_mul {F G : PowerSeries ℂ} {f g : ℂ → ℂ} (hF : Rep F f) (hG : Rep G g) :
    Rep (F * G) (fun t => f t * g t) := by
  intro t ht
  obtain ⟨s1, h1⟩ := hF t ht
  obtain ⟨s2, h2⟩ := hG t ht
  have e : (fun n => PowerSeries.coeff n (F * G) * t ^ n) = fun n =>
      ∑ kl ∈ Finset.antidiagonal n, (PowerSeries.coeff kl.1 F * t ^ kl.1) *
        (PowerSeries.coeff kl.2 G * t ^ kl.2) := by
    funext n
    rw [PowerSeries.coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    rw [Finset.mem_antidiagonal] at hkl
    rw [← hkl, pow_add]; ring
  have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm s1 s2
  refine ⟨hs.congr fun n => by rw [congrFun e n], ?_⟩
  have := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm s1 s2
  rw [h1.tsum_eq, h2.tsum_eq] at this
  rw [e]
  show HasSum _ (f t * g t)
  rw [this]
  exact hs.of_norm.hasSum

lemma rep_pow {F : PowerSeries ℂ} {f : ℂ → ℂ} (hF : Rep F f) (n : ℕ) :
    Rep (F ^ n) (fun t => f t ^ n) := by
  induction n with
  | zero => simpa using rep_C 1
  | succ n ih => simpa [pow_succ] using rep_mul ih hF

lemma rep_prod {ι : Type*} (s : Finset ι) (F : ι → PowerSeries ℂ) (f : ι → ℂ → ℂ)
    (hF : ∀ i, Rep (F i) (f i)) : Rep (∏ i ∈ s, F i) (fun t => ∏ i ∈ s, f i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rep_C 1
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact rep_mul (hF i) ih

lemma rep_log : Rep (PowerSeries.log ℂ) (fun t => Complex.log (1 + t)) := by
  intro t ht
  have e : (fun n => PowerSeries.coeff n (PowerSeries.log ℂ) * t ^ n) =
      fun n : ℕ => (-1) ^ (n + 1) * t ^ n / n := by
    funext n
    rw [PowerSeries.coeff_log]
    split_ifs with h
    · simp [h]
    · simp [div_eq_mul_inv]; ring
  refine ⟨?_, e ▸ Complex.hasSum_taylorSeries_log ht⟩
  refine (summable_geometric_of_lt_one (norm_nonneg _) ht).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun n => ?_)
  rw [congrFun e n, norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · rw [div_le_iff₀ (by simp; omega)]
    have : (1 : ℝ) ≤ ‖(n : ℂ)‖ := by simp; exact_mod_cast h
    nlinarith [pow_nonneg (norm_nonneg t) n]

lemma coeff_eq_cauchy {F : PowerSeries ℂ} {G : ℂ → ℂ} (hF : Rep F G) (ell : ℕ) :
    PowerSeries.coeff ell F = cauchyPowerSeries G 0 (1 / 2) ell (fun _ => (1 : ℂ)) := by
  set c : ℕ → ℂ := fun n => PowerSeries.coeff n F
  set P := FormalMultilinearSeries.ofScalars ℂ c
  have h34 : ‖((3 / 4 : ℝ) : ℂ)‖ < 1 := by rw [Complex.norm_real]; norm_num [abs_of_pos]
  have hP : HasFPowerSeriesOnBall G P 0 (3 / 4 : NNReal) := by
    refine ⟨?_, by norm_num, ?_⟩
    · apply P.le_radius_of_summable_norm
      have := (hF _ h34).1
      refine this.congr fun n => ?_
      simp only [P, FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow,
        Complex.norm_real, c]
      norm_num [abs_of_pos]
    · intro y hy
      have hy' : ‖y‖ < 1 := by
        rw [mem_eball_zero_iff] at hy
        have : ‖y‖₊ < (3 / 4 : NNReal) := by exact_mod_cast hy
        have : ‖y‖ < 3 / 4 := by exact_mod_cast this
        linarith
      rw [zero_add]
      simpa [P, FormalMultilinearSeries.ofScalars_apply_eq, c, smul_eq_mul, mul_comm] using (hF y hy').2
  have hd : DifferentiableOn ℂ G (Metric.closedBall 0 (1 / 2 : NNReal)) := by
    refine hP.differentiableOn.mono fun y hy => ?_
    rw [mem_eball_zero_iff]
    rw [Metric.mem_closedBall, dist_zero_right] at hy
    have : ‖y‖ < 3 / 4 := by
      have : ((1 / 2 : NNReal) : ℝ) = 1 / 2 := by norm_num
      linarith
    have : ‖y‖₊ < (3 / 4 : NNReal) := by
      rw [← NNReal.coe_lt_coe]; simpa using this
    exact_mod_cast this
  have hQ := hd.hasFPowerSeriesOnBall (by norm_num)
  have heq := hP.hasFPowerSeriesAt.eq_formalMultilinearSeries hQ.hasFPowerSeriesAt
  have h2 : ((1 / 2 : NNReal) : ℝ) = 1 / 2 := by norm_num
  rw [h2] at heq
  rw [← heq]
  simp [P, c]

open MvPolynomial in
lemma coeff_prod_C_add_X {σ : Type*} [Fintype σ] [DecidableEq σ] {R : Type*} [CommRing R]
    (Q : R) (a : σ → ℕ) (A : σ →₀ ℕ) :
    (∏ i, (C Q + X i) ^ (a i) : MvPolynomial σ R).coeff A =
      ∏ i, ((a i).choose (A i) : R) * Q ^ (a i - A i) := by
  have h1 : ∀ i, (C Q + X i : MvPolynomial σ R) ^ (a i) = ∑ k ∈ Finset.range (a i + 1),
      monomial (Finsupp.single i k) (((a i).choose k : R) * Q ^ (a i - k)) := by
    intro i
    rw [add_comm, add_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [X_pow_eq_monomial, ← C_pow,
      show (((a i).choose k : ℕ) : MvPolynomial σ R) = C ((a i).choose k : R) from
        (map_natCast C _).symm,
      mul_assoc, ← C_mul, mul_comm, C_mul_monomial, mul_one, mul_comm]
  rw [Finset.prod_congr rfl (fun i _ => h1 i), Finset.prod_univ_sum, coeff_sum]
  simp_rw [← monomial_sum_prod, coeff_monomial]
  have hsum : ∀ x : σ → ℕ, (∑ i, Finsupp.single i (x i)) = A ↔ x = ⇑A := by
    intro x
    constructor
    · intro h; funext i
      have := congrArg (fun f : σ →₀ ℕ => f i) h
      simpa [Finsupp.finsetSum_apply, Finsupp.single_apply] using this
    · rintro rfl; exact Finsupp.univ_sum_single A
  rw [Finset.sum_eq_single (⇑A)]
  · rw [if_pos ((hsum _).2 rfl)]
  · intro x _ hx
    rw [if_neg (fun h => hx ((hsum x).1 h))]
  · intro hA
    rw [if_pos ((hsum _).2 rfl)]
    rw [Fintype.mem_piFinset] at hA
    push Not at hA
    obtain ⟨i, hi⟩ := hA
    rw [Finset.mem_range, not_lt] at hi
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]

end S45PM

lemma S45PM.T_eq {m : ℕ} (j h : ℕ) (a : Fin m → ℕ) (A : Fin m →₀ ℕ) :
    (periodMonomial j h a).coeff A =
      PowerSeries.C ((Finset.univ.prod (fun i : Fin m => (a i).choose (A i)) : ℕ) : ℂ) *
      ((1 + PowerSeries.X) ^ h * (PowerSeries.C ((j : ℂ) * FiniteMinorAnalysis_690acb6f.period) +
        PowerSeries.log ℂ) ^ (Finset.univ.sum (fun i : Fin m => a i - A i))) := by
  unfold periodMonomial
  rw [MvPolynomial.coeff_C_mul, S45PM.coeff_prod_C_add_X, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Nat.cast_prod, map_prod]
  simp only [map_natCast]
  ring

open S45PM in
theorem S45PM.pm_sol
    {m : ℕ} (j h ell : ℕ) (a : Fin m → ℕ) (A : Fin m →₀ ℕ) :
    PowerSeries.coeff ell ((periodMonomial j h a).coeff A) =
      cauchyPowerSeries
        (fun t : ℂ => columnFunction h a A
          ((j : ℂ) * period + Complex.log (1 + t)))
        0 (1 / 2) ell (fun _ => (1 : ℂ)) := by
  apply coeff_eq_cauchy
  unfold periodMonomial
  rw [MvPolynomial.coeff_C_mul, coeff_prod_C_add_X]
  have hT : ((1 + PowerSeries.X) ^ h * ∏ i, (((a i).choose (A i) : ℕ) : PowerSeries ℂ) *
      (PowerSeries.C ((j : ℂ) * period) + PowerSeries.log ℂ) ^ (a i - A i)) =
      (PowerSeries.C 1 + PowerSeries.X) ^ h * ∏ i, PowerSeries.C (((a i).choose (A i) : ℕ) : ℂ) *
      (PowerSeries.C ((j : ℂ) * period) + PowerSeries.log ℂ) ^ (a i - A i) := by
    simp only [map_one, map_natCast]
  rw [hT]
  have hR := rep_mul (rep_pow (rep_add (rep_C 1) rep_X) h)
    (rep_prod Finset.univ _ _ (fun i => rep_mul (rep_C (((a i).choose (A i) : ℕ) : ℂ))
      (rep_pow (rep_add (rep_C ((j : ℂ) * period)) rep_log) (a i - A i))))
  refine rep_congr hR fun t ht => ?_
  have ht1 : (1 : ℂ) + t ≠ 0 := by
    intro h0
    have : t = -1 := by linear_combination h0
    rw [this, norm_neg, norm_one] at ht
    exact lt_irrefl _ ht
  simp only [columnFunction]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Nat.cast_prod]
  have hexp : Complex.exp ((h : ℂ) * ((j : ℂ) * period + Complex.log (1 + t))) = (1 + t) ^ h := by
    have : (h : ℂ) * ((j : ℂ) * period + Complex.log (1 + t)) =
        ((h * j : ℕ) : ℂ) * (2 * Real.pi * Complex.I) + (h : ℂ) * Complex.log (1 + t) := by
      simp only [period]; push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, one_mul, Complex.exp_nat_mul,
      Complex.exp_log ht1]
  rw [hexp]
  ring

theorem solution {m : ℕ} (j h ell : ℕ) (a : Fin m → ℕ) (A : Fin m →₀ ℕ) : ((Finset.univ.prod (fun i : Fin m => (a i).choose (A i)) : ℕ) : ℂ) * PowerSeries.coeff ell ((1 + PowerSeries.X) ^ h * (PowerSeries.C ((j : ℂ) * FiniteMinorAnalysis_690acb6f.period) + PowerSeries.log ℂ) ^ (Finset.univ.sum (fun i : Fin m => a i - A i))) = cauchyPowerSeries (fun t : ℂ => columnFunction h a A ((j : ℂ) * FiniteMinorAnalysis_690acb6f.period + Complex.log (1 + t))) 0 (1 / 2) ell (fun _ => (1 : ℂ)) := by
  rw [← S45PM.pm_sol, S45PM.T_eq, PowerSeries.coeff_C_mul]
