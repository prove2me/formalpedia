-- Prove2me | solution 1 for OAI.PiExponent.MinorTranslationData.periodMonomial_formal_coeff_eq_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T05:42:46.826565+00:00
-- url     : https://prove2.me/submissions/53975a42-a1d1-4f8e-a490-991c0e91c0da

import Definitions.Def_OAI_PiExponent_MinorTranslationData
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Analytic.OfScalars
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.MinorTranslationData
open Filter Topology

namespace S105PM

def Rep (F : PowerSeries ℂ) (g : ℂ → ℂ) : Prop :=
  ∀ t : ℂ, ‖t‖ < 1 → Summable (fun n => ‖PowerSeries.coeff n F * t ^ n‖) ∧
    HasSum (fun n => PowerSeries.coeff n F * t ^ n) (g t)

lemma rep_congr {F : PowerSeries ℂ} {g g' : ℂ → ℂ} (h : Rep F g) (e : ∀ t : ℂ, ‖t‖ < 1 → g t = g' t) :
    Rep F g' := fun t ht => ⟨(h t ht).1, e t ht ▸ (h t ht).2⟩

lemma rep_C (a : ℂ) : Rep (PowerSeries.C a) (fun _ => a) := by
  intro t _
  have hf : (fun n => PowerSeries.coeff n (PowerSeries.C a) * t ^ n) = fun n => if n = 0 then a else 0 := by
    funext n; rw [PowerSeries.coeff_C]; split_ifs with h <;> simp [h]
  refine ⟨?_, ?_⟩
  · simp_rw [congrFun hf]
    apply summable_of_ne_finset_zero (s := {0}); intro n hn; simp at hn; simp [hn]
  · rw [hf]; convert hasSum_ite_eq 0 a using 1

lemma rep_X : Rep PowerSeries.X (fun t => t) := by
  intro t _
  have hf : (fun n => PowerSeries.coeff n (PowerSeries.X : PowerSeries ℂ) * t ^ n) = fun n => if n = 1 then t else 0 := by
    funext n; rw [PowerSeries.coeff_X]; split_ifs with h <;> simp [h]
  refine ⟨?_, ?_⟩
  · simp_rw [congrFun hf]
    apply summable_of_ne_finset_zero (s := {1}); intro n hn; simp at hn; simp [hn]
  · rw [hf]; convert hasSum_ite_eq 1 t using 1

lemma rep_add {F G : PowerSeries ℂ} {f g : ℂ → ℂ} (hF : Rep F f) (hG : Rep G g) :
    Rep (F + G) (fun t => f t + g t) := by
  intro t ht
  obtain ⟨s1, h1⟩ := hF t ht
  obtain ⟨s2, h2⟩ := hG t ht
  simp only [map_add, add_mul]
  exact ⟨(s1.add s2).of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => norm_add_le _ _), h1.add h2⟩

lemma rep_mul {F G : PowerSeries ℂ} {f g : ℂ → ℂ} (hF : Rep F f) (hG : Rep G g) :
    Rep (F * G) (fun t => f t * g t) := by
  intro t ht
  obtain ⟨s1, h1⟩ := hF t ht
  obtain ⟨s2, h2⟩ := hG t ht
  have heq : (fun n => PowerSeries.coeff n (F * G) * t ^ n) = fun n =>
      ∑ kl ∈ Finset.antidiagonal n, (PowerSeries.coeff kl.1 F * t ^ kl.1) * (PowerSeries.coeff kl.2 G * t ^ kl.2) := by
    funext n
    rw [PowerSeries.coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    rw [Finset.mem_antidiagonal] at hkl
    rw [← hkl, pow_add]; ring
  have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm s1 s2
  refine ⟨hs.congr (fun n => by rw [congrFun heq n]), ?_⟩
  rw [heq]
  show HasSum _ (f t * g t)
  have := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm s1 s2
  rw [h1.tsum_eq, h2.tsum_eq] at this
  rw [this]
  exact hs.of_norm.hasSum

lemma rep_pow {F : PowerSeries ℂ} {f : ℂ → ℂ} (hF : Rep F f) (n : ℕ) :
    Rep (F ^ n) (fun t => f t ^ n) := by
  induction n with
  | zero => simpa using rep_C 1
  | succ n ih => simpa [pow_succ] using rep_mul ih hF

lemma norm_coeff_log (n : ℕ) : ‖PowerSeries.coeff n (PowerSeries.log ℂ)‖ ≤ 1 := by
  rw [PowerSeries.coeff_log]
  split_ifs with h
  · simp
  · rw [eq_ratCast, Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_natCast,
      norm_div, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast]
    have : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 h
    rw [div_le_one (by linarith)]; exact this

lemma rep_log : Rep (PowerSeries.log ℂ) (fun t => Complex.log (1 + t)) := by
  intro t ht
  have hf : (fun n => PowerSeries.coeff n (PowerSeries.log ℂ) * t ^ n) =
      fun n : ℕ => (-1) ^ (n + 1) * t ^ n / n := by
    funext n
    rw [PowerSeries.coeff_log]
    split_ifs with h
    · subst h; simp
    · rw [eq_ratCast]; push_cast; ring
  refine ⟨?_, by rw [hf]; exact Complex.hasSum_taylorSeries_log ht⟩
  refine (summable_geometric_of_norm_lt_one ht).norm.of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_left (by positivity) (norm_coeff_log n)

/-- From a representation on the unit disc to the Cauchy coefficient at radius 1/2. -/
lemma cauchy_eq {F : PowerSeries ℂ} {g : ℂ → ℂ} (hF : Rep F g) (ell : ℕ) :
    cauchyPowerSeries g 0 (1 / 2) ell (fun _ => (1 : ℂ)) = PowerSeries.coeff ell F := by
  set c : ℕ → ℂ := fun n => PowerSeries.coeff n F
  set p := FormalMultilinearSeries.ofScalars ℂ c
  have hrad : ((3 / 4 : NNReal) : ENNReal) ≤ p.radius := by
    apply FormalMultilinearSeries.le_radius_of_summable
    have := (hF (3 / 4 : ℂ) (by norm_num)).1
    refine this.congr fun n => ?_
    simp [p, FormalMultilinearSeries.ofScalars_norm, c]
  have hp : HasFPowerSeriesOnBall g p 0 ((3 / 4 : NNReal) : ENNReal) := by
    refine ⟨hrad, by simp, fun {y} hy => ?_⟩
    have hy' : ‖y‖ < 1 := by
      rw [Metric.eball_coe, Metric.mem_ball, dist_zero_right] at hy
      exact hy.trans (by norm_num)
    rw [zero_add]
    have := (hF y hy').2
    refine this.congr_fun ?_
    intro n
    rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  have hd : DifferentiableOn ℂ g (Metric.closedBall 0 ((1 / 2 : NNReal) : ℝ)) := by
    refine hp.differentiableOn.mono ?_
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    rw [Metric.eball_coe, Metric.mem_ball, dist_zero_right]
    have : ((1 / 2 : NNReal) : ℝ) = 1 / 2 := by norm_num
    rw [this] at hz
    have : ((3 / 4 : NNReal) : ℝ) = 3 / 4 := by norm_num
    rw [this]; linarith
  have hc := hd.hasFPowerSeriesOnBall (by norm_num)
  have heq := hc.hasFPowerSeriesAt.eq_formalMultilinearSeries hp.hasFPowerSeriesAt
  have h12 : ((1 / 2 : NNReal) : ℝ) = 1 / 2 := by norm_num
  rw [h12] at heq
  rw [heq, FormalMultilinearSeries.ofScalars_apply_eq, one_pow, smul_eq_mul, mul_one]

end S105PM

theorem solution
    {m : ℕ} (j h ell : ℕ) (a : Fin m → ℕ) (A : Fin m →₀ ℕ) :
    PowerSeries.coeff ell
        (PowerSeries.C ((∏ i, (a i).choose (A i) : ℕ) : ℂ) *
          (PowerSeries.C ((j : ℂ) * period) + PowerSeries.log ℂ) ^
            (∑ i : Fin m, (a i - A i)) *
          (1 + PowerSeries.X) ^ h) =
      cauchyPowerSeries
        (fun t : ℂ =>
          ((∏ i, (a i).choose (A i) : ℕ) : ℂ) *
            Complex.exp ((h : ℂ) * ((j : ℂ) * period + Complex.log (1 + t))) *
            ((j : ℂ) * period + Complex.log (1 + t)) ^
              (∑ i : Fin m, (a i - A i)))
        0 (1 / 2) ell (fun _ => (1 : ℂ)) := by
  open S105PM in
  have hR := rep_mul (rep_mul (rep_C ((∏ i, (a i).choose (A i) : ℕ) : ℂ))
    (rep_pow (rep_add (rep_C ((j : ℂ) * period)) rep_log) (∑ i : Fin m, (a i - A i))))
    (rep_pow (rep_add (rep_C 1) rep_X) h)
  rw [map_one] at hR
  refine (cauchy_eq (rep_congr hR ?_) ell).symm
  intro t ht
  have h1 : (1 : ℂ) + t ≠ 0 := by
    intro h0
    have : t = -1 := by linear_combination h0
    rw [this, norm_neg, norm_one] at ht; exact lt_irrefl _ ht
  have hexp : Complex.exp ((h : ℂ) * ((j : ℂ) * period + Complex.log (1 + t))) = (1 + t) ^ h := by
    rw [Complex.exp_nat_mul, Complex.exp_add, period, Complex.exp_nat_mul_two_pi_mul_I, one_mul,
      Complex.exp_log h1]
  rw [hexp]; ring
