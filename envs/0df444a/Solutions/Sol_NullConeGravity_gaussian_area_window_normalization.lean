-- Prove2me | solution 1 for NullConeGravity.gaussian_area_window_normalization
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T20:37:10.615232+00:00
-- url     : https://prove2.me/submissions/6d77ec90-96ac-4fc1-aa7c-c29af960f12f

import Theorems.Thm_NullConeGravity_schwarzschild_mass_area_change_of_variables
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Normalization of the Gaussian area window

The integral is taken over the window center at a fixed nonnegative area eigenvalue.
The mass substitution imports the accepted Schwarzschild area-to-mass theorem.
See [Chandrasekaran, Eq. (5.66)](https://arxiv.org/html/2611.34924v1#S5.E66).
-/

open Set MeasureTheory Filter
open scoped Topology
namespace NullConeGravity

private noncomputable def window (s t : ℝ) : ℝ :=
  Real.exp (-((s - t) ^ 2) / (4 * t))

/-- Apply the accepted change of variables on a positive interval. Clipping the argument at
its lower endpoint gives the globally continuous weight required by that theorem. -/
private theorem window_mass (s a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a^2..b^2, window s t / Real.sqrt t) =
      2 * ∫ m in a..b, window s (m^2) := by
  let F (t : ℝ) := window s (max (a^2) t)
  have hmax : Continuous (fun t : ℝ => max (a^2) t) := continuous_const.max continuous_id
  have hF : Continuous F := Real.continuous_exp.comp
    (((continuous_const.sub hmax).pow 2).neg.div (continuous_const.mul hmax)
      (fun t => mul_ne_zero (by norm_num) (lt_of_lt_of_le (sq_pos_of_pos ha)
        (le_max_left (a^2) t)).ne'))
  have hcut := schwarzschild_mass_area_change_of_variables 1 a b (by norm_num) ha hab F hF
  simp only [one_mul, Real.sqrt_one, mul_one] at hcut
  have heq {t : ℝ} (ht : a^2 ≤ t) : F t = window s t := by simp [F,max_eq_right ht]
  have hab2 : a^2 ≤ b^2 := pow_le_pow_left₀ ha.le hab 2
  calc
    _ = ∫ t in a^2..b^2, F t / Real.sqrt t := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only
      rw [heq (((uIcc_of_le hab2) ▸ ht).1)]
    _ = 2 * ∫ m in a..b, F (m^2) := hcut
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro m hm
      exact heq (pow_le_pow_left₀ ha.le (((uIcc_of_le hab) ▸ hm).1) 2)

/-- The positive inverse of the substitution `x = (m^2 - s) / (2*m)` when `s > 0`. -/
private noncomputable def mass (s x : ℝ) := x + Real.sqrt (x^2+s)
private noncomputable def skew (s x : ℝ) := x / Real.sqrt (x^2+s)

private theorem mass_pos {s : ℝ} (hs : 0 < s) (x : ℝ) : 0 < mass s x := by
  have h : -x < Real.sqrt (x^2+s) := Real.lt_sqrt_of_sq_lt (by nlinarith)
  unfold mass
  linarith

private theorem mass_deriv {s : ℝ} (hs : 0 < s) (x : ℝ) :
    HasDerivAt (mass s) (1 + skew s x) x := by
  have h : HasDerivAt (fun y : ℝ => y^2+s) (2*x) x := by
    simpa using (hasDerivAt_pow 2 x).add_const s
  have hpos : 0 < x^2+s := by positivity
  have hd := (hasDerivAt_id x).add (h.sqrt hpos.ne')
  have he : 2*x / (2*Real.sqrt (x^2+s)) = skew s x := by
    unfold skew
    rw [mul_div_mul_left _ _ (by norm_num : (2:ℝ) ≠ 0)]
  rw [he] at hd
  exact hd

private theorem mass_mono {s : ℝ} (hs : 0 < s) : StrictMono (mass s) := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(mass_deriv hs x).deriv]
  have h : 0 < Real.sqrt (x^2+s) := Real.sqrt_pos.2 (by positivity)
  have hm := mass_pos hs x
  unfold mass at hm
  unfold skew
  rw [← div_self h.ne', ← add_div]
  exact div_pos (by linarith) h

private theorem window_mass_eval {s : ℝ} (hs : 0 < s) (x : ℝ) :
    window s (mass s x ^ 2) = Real.exp (-(x^2)) := by
  have hm := mass_pos hs x
  have hroot := Real.sq_sqrt (show 0 ≤ x^2+s by positivity)
  have halg : s - mass s x ^ 2 = -(2*x*mass s x) := by
    unfold mass
    nlinarith
  unfold window
  congr 1
  rw [halg]
  field_simp
  ring

private noncomputable def gaussian (x : ℝ) := Real.exp (-(x^2))

private theorem gaussian_cont : Continuous gaussian :=
  Real.continuous_exp.comp (continuous_id.pow 2).neg

private theorem skew_cont {s : ℝ} (hs : 0 < s) : Continuous (skew s) :=
  continuous_id.div (Real.continuous_sqrt.comp ((continuous_id.pow 2).add continuous_const))
    (fun x => (Real.sqrt_pos.2 (by positivity)).ne')

private theorem window_contAt (s : ℝ) {t : ℝ} (ht : 0 < t) : ContinuousAt (window s) t := by
  apply Real.continuous_exp.continuousAt.comp
  exact (((continuousAt_const.sub continuousAt_id).pow 2).neg.div
    (continuousAt_const.mul continuousAt_id) (mul_ne_zero (by norm_num) ht.ne'))

/-- In the new variable the Jacobian is one plus an odd function. Its odd contribution
integrates to zero on every symmetric interval. -/
private theorem symmetric_window {s R : ℝ} (hs : 0 < s) (hR : 0 ≤ R) :
    (∫ t in (mass s (-R))^2..(mass s R)^2, window s t / Real.sqrt t) =
      2 * ∫ x in -R..R, gaussian x := by
  have hmass := window_mass s (mass s (-R)) (mass s R)
    (mass_pos hs _) ((mass_mono hs).monotone (by linarith))
  rw [hmass]
  congr 1
  have hg : ContinuousOn (fun m => window s (m^2)) ((mass s) '' uIcc (-R) R) := by
    rintro _ ⟨x, _, rfl⟩
    have hsq : ContinuousAt (fun y : ℝ => y ^ 2) (mass s x) := by fun_prop
    exact (ContinuousAt.comp (f:=fun y : ℝ => y^2) (window_contAt s (pow_pos (mass_pos hs x) 2)) hsq).continuousWithinAt
  have hsub := intervalIntegral.integral_comp_mul_deriv' (fun x _ => mass_deriv hs x)
    (continuous_const.add (skew_cont hs)).continuousOn hg
  let odd (x : ℝ) := gaussian x * skew s x
  have ho (x : ℝ) : odd (-x) = -odd x := by simp [odd, gaussian, skew, div_eq_mul_inv]
  have hz : (∫ x in -R..R, odd x) = 0 := by
    have h := intervalIntegral.integral_comp_neg (a := -R) (b := R) odd
    simp only [neg_neg, ho, intervalIntegral.integral_neg] at h
    linarith
  calc
    _ = ∫ x in -R..R, ((fun m => window s (m^2)) ∘ mass s) x * (1 + skew s x) := hsub.symm
    _ = ∫ x in -R..R, gaussian x + odd x := by
      apply intervalIntegral.integral_congr
      intro x _
      change window s (mass s x ^ 2) * (1 + skew s x) = gaussian x + gaussian x * skew s x
      rw [window_mass_eval hs]
      unfold gaussian
      ring
    _ = _ := by
      have hi : IntervalIntegrable odd volume (-R) R := (gaussian_cont.mul (skew_cont hs)).intervalIntegrable ..
      rw [intervalIntegral.integral_add (f := gaussian) (g := odd) (gaussian_cont.intervalIntegrable ..) hi, hz, add_zero]

private theorem mass_onto {s m : ℝ} (hm : 0 < m) (hs : 0 < s) :
    ∃ x, mass s x = m := by
  let x := (m^2 - s) / (2*m)
  have hx : 2*m*x = m^2-s := by dsimp [x]; field_simp
  have hpos : 0 < m-x := by
    apply (mul_pos_iff_of_pos_left (show 0 < 2*m by positivity)).mp
    nlinarith [sq_nonneg m]
  have he : x^2+s = (m-x)^2 := by nlinarith
  refine ⟨x, ?_⟩
  unfold mass
  rw [he, Real.sqrt_sq hpos.le]
  ring

/-- The symmetric windows exhaust the positive half-line. Positivity lets their integrals
determine the full integral without any prior assumption of integrability. -/
private theorem positive_window_integral {s : ℝ} (hs : 0 < s) :
    (∫ t in Ioi 0, window s t / Real.sqrt t) = 2 * Real.sqrt Real.pi := by
  let lo (n : ℕ) := (mass s (-(n : ℝ)))^2
  let hi (n : ℕ) := (mass s (n : ℝ))^2
  let cut (n : ℕ) := Ioc (lo n) (hi n)
  let k (t : ℝ) := window s t / Real.sqrt t
  have low (n : ℕ) : 0 < lo n := sq_pos_of_pos (mass_pos hs _)
  have order (n : ℕ) : lo n ≤ hi n := pow_le_pow_left₀ (mass_pos hs _).le
    ((mass_mono hs).monotone (_root_.neg_le_self (Nat.cast_nonneg n))) 2
  have sub (n : ℕ) : cut n ⊆ Ioi (0:ℝ) := fun _ h => (low n).trans h.1
  have cover : AECover (volume.restrict (Ioi (0:ℝ))) atTop cut := by
    apply aecover_restrict_of_ae_imp measurableSet_Ioi _ (fun n => measurableSet_Ioc)
    filter_upwards with t
    intro ht
    obtain ⟨x,hx⟩ := mass_onto (Real.sqrt_pos.2 ht) hs
    have ev : ∀ᶠ n : ℕ in atTop, |x| < (n:ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop |x|)
    filter_upwards [ev] with n hn
    obtain ⟨hleft,hright⟩ := abs_lt.mp hn
    have hl := (sq_lt_sq₀ (mass_pos hs _).le (mass_pos hs _).le).2 (mass_mono hs hleft)
    have hu := (sq_lt_sq₀ (mass_pos hs _).le (mass_pos hs _).le).2 (mass_mono hs hright)
    rw [hx, Real.sq_sqrt ht.le] at hl hu
    exact ⟨hl,hu.le⟩
  have restr (n : ℕ) : (volume.restrict (Ioi (0:ℝ))).restrict (cut n) =
      volume.restrict (cut n) := by
    rw [Measure.restrict_restrict (show MeasurableSet (cut n) from measurableSet_Ioc),
      inter_eq_left.mpr (sub n)]
  have hint (n : ℕ) : IntegrableOn k (cut n) (volume.restrict (Ioi (0:ℝ))) := by
    change Integrable k ((volume.restrict _).restrict _)
    rw [restr]
    have hc : ContinuousOn k (Icc (lo n) (hi n)) := by
      intro t ht
      have hp := (low n).trans_le ht.1
      exact ((window_contAt s hp).div Real.continuous_sqrt.continuousAt (Real.sqrt_pos.2 hp).ne').continuousWithinAt
    exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have heq (n : ℕ) : (∫ t in cut n, k t ∂volume.restrict (Ioi 0)) =
      2 * ∫ x in -(n:ℝ)..(n:ℝ), gaussian x := by
    rw [restr]
    change (∫ t in Ioc (lo n) (hi n), k t) = _
    rw [← intervalIntegral.integral_of_le (order n)]
    exact symmetric_window hs (Nat.cast_nonneg n)
  have gaussInt : Integrable gaussian := by
    unfold gaussian
    simpa using (integrable_exp_neg_mul_sq (b:=1) zero_lt_one)
  have gaussValue : (∫ x : ℝ, gaussian x) = Real.sqrt Real.pi := by
    simpa [gaussian] using integral_gaussian (1:ℝ)
  have lim := intervalIntegral_tendsto_integral gaussInt
    (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop (R:=ℝ))) (tendsto_natCast_atTop_atTop (R:=ℝ))
  rw [gaussValue] at lim
  refine cover.integral_eq_of_tendsto_of_nonneg_ae _ ?_ hint ?_
  · filter_upwards with t
    exact div_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)
  · exact (tendsto_const_nhds.mul lim).congr (fun n => (heq n).symm)

private theorem sqrt_four : Real.sqrt 4 = 2 :=
  (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)

/-- At zero area the substitution `t = m^2` gives the ordinary half-Gaussian integral. -/
private theorem zero_window_integral :
    (∫ t in Ioi 0, window 0 t / Real.sqrt t) = 2 * Real.sqrt Real.pi := by
  let k (t : ℝ) := window 0 t / Real.sqrt t
  have hsub := integral_comp_rpow_Ioi_of_pos (g:=k) (show 0 < (2:ℝ) by norm_num)
  calc
    _ = ∫ x in Ioi (0:ℝ), (2*x^((2:ℝ)-1)) • k (x^(2:ℝ)) := hsub.symm
    _ = ∫ x in Ioi (0:ℝ), 2 * Real.exp (-(1/4:ℝ)*x^2) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hp : 0 < x := hx
      simp only [show (2:ℝ)-1=1 by norm_num, Real.rpow_one, Real.rpow_two, smul_eq_mul]
      change 2*x*(window 0 (x^2)/Real.sqrt (x^2)) = _
      rw [Real.sqrt_sq hp.le]
      have he : window 0 (x^2) = Real.exp (-(1/4:ℝ)*x^2) := by
        unfold window
        congr 1
        field_simp [hp.ne']
        ring
      rw [he]
      field_simp [hp.ne']
    _ = _ := by
      rw [integral_const_mul,integral_gaussian_Ioi]
      rw [show Real.pi / (1 / 4) = 4 * Real.pi by ring,
          Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4), sqrt_four]
      ring

end NullConeGravity

open NullConeGravity

theorem solution (s : ℝ) (hs : 0 ≤ s) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-((s - t) ^ 2) / (4 * t)) / Real.sqrt (4 * Real.pi * t)) = 1 := by
  have hu : (∫ t in Ioi 0, window s t / Real.sqrt t) = 2 * Real.sqrt Real.pi := by
    rcases hs.eq_or_lt with hz | hp
    · subst s
      exact zero_window_integral
    · exact positive_window_integral hp
  calc
    _ = ∫ t in Ioi (0:ℝ), (window s t / Real.sqrt t) / (2 * Real.sqrt Real.pi) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [Real.sqrt_mul (show (0:ℝ) ≤ 4*Real.pi by positivity),
        Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4),sqrt_four]
      norm_num [window,div_div,mul_comm]
    _ = 1 := by
      rw [integral_div, hu, div_self (by positivity)]
