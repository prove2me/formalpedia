-- Prove2me | solution 1 for Helfgott.reference_etaCircle_etaStar_main_convolution_lower_tight
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T04:46:43.183411+00:00
-- url     : https://prove2.me/submissions/09bb066f-6712-49a6-9a45-98e9a6bd161a

import Definitions.Def_Helfgott_Smoothings
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Real.Pi.Bounds

section
open MeasureTheory Filter Set
open scoped Topology

namespace Helfgott

private lemma body_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s : ℝ => s^3 * (2-s)^3 * Real.exp (-((s-1)^2)/2))
      (-(t-1) * (1-(t-1)^2)^2 * (7-(t-1)^2) * Real.exp (-((t-1)^2)/2)) t := by
  convert! ((((hasDerivAt_id t).pow 3).mul
    (((hasDerivAt_const t (2 : ℝ)).sub (hasDerivAt_id t)).pow 3)).mul
    (((((hasDerivAt_id t).sub_const 1).pow 2).neg.div_const 2).exp)) using 1 <;>
    simp <;> ring

theorem etaCircle_hasDerivAt (t : ℝ) :
    HasDerivAt etaCircle
      ((Set.Icc (0 : ℝ) 2).indicator (fun t =>
        -(t-1) * (1-(t-1)^2)^2 * (7-(t-1)^2) * Real.exp (-((t-1)^2)/2)) t) t := by
  by_cases ht : t ∈ Set.Icc (0 : ℝ) 2
  · rw [Set.indicator_of_mem ht]
    by_cases hboundary : t = 0 ∨ t = 2
    · have hval : etaCircle t = 0 := by
        rcases hboundary with rfl | rfl <;> norm_num [etaCircle]
      have hd : -(t-1) * (1-(t-1)^2)^2 * (7-(t-1)^2) * Real.exp (-((t-1)^2)/2) = 0 := by
        rcases hboundary with rfl | rfl <;> norm_num
      rw [hd]
      have hinside : HasDerivWithinAt etaCircle 0 (Set.Icc (0 : ℝ) 2) t := by
        have h := (body_hasDerivAt t).hasDerivWithinAt (s := Set.Icc (0 : ℝ) 2)
        rw [hd] at h
        apply h.congr
        · intro x hx; simp only [etaCircle, Set.indicator_of_mem hx]
        · simp only [etaCircle, Set.indicator_of_mem ht]
      have houtside : HasDerivWithinAt etaCircle 0 (Set.Icc (0 : ℝ) 2)ᶜ t := by
        apply (hasDerivAt_const t (0 : ℝ)).hasDerivWithinAt.congr
        · intro x hx; simp only [etaCircle, Set.indicator_of_notMem hx]
        · exact hval
      simpa only [Set.union_compl_self, hasDerivWithinAt_univ] using hinside.union houtside
    · have h0 : 0 < t := lt_of_le_of_ne ht.1 (by tauto)
      have h2 : t < 2 := lt_of_le_of_ne ht.2 (by tauto)
      apply (body_hasDerivAt t).congr_of_eventuallyEq
      filter_upwards [Icc_mem_nhds h0 h2] with x hx
      simp only [etaCircle, Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem ht]
    apply (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds ht] with x hx
    simp only [etaCircle, Set.indicator_of_notMem hx]

lemma etaCircle_continuous : Continuous etaCircle :=
  continuous_iff_continuousAt.mpr (fun t => (etaCircle_hasDerivAt t).continuousAt)

lemma etaCircle_nonneg (t : ℝ) : 0 ≤ etaCircle t := by
  by_cases ht : t ∈ Set.Icc (0 : ℝ) 2
  · simp only [etaCircle, Set.indicator_of_mem ht]
    have h2 : 0 ≤ 2-t := sub_nonneg.mpr ht.2
    have h0 : 0 ≤ t := ht.1
    positivity
  · simp only [etaCircle, Set.indicator_of_notMem ht, le_refl]

lemma etaCircle_symmetric (t : ℝ) : etaCircle (2-t) = etaCircle t := by
  by_cases ht : t ∈ Set.Icc (0 : ℝ) 2
  · have ht' : 2-t ∈ Set.Icc (0 : ℝ) 2 := by constructor <;> linarith [ht.1,ht.2]
    simp only [etaCircle, Set.indicator_of_mem ht, Set.indicator_of_mem ht']
    have he : -((2-t-1)^2)/2 = -((t-1)^2)/2 := by ring
    rw [he]
    ring
  · have ht' : 2-t ∉ Set.Icc (0 : ℝ) 2 := by
      intro h; apply ht; constructor <;> linarith [h.1,h.2]
    simp only [etaCircle, Set.indicator_of_notMem ht, Set.indicator_of_notMem ht']

lemma etaCircle_hasCompactSupport : HasCompactSupport etaCircle := by
  apply HasCompactSupport.intro (K := Set.Icc (0 : ℝ) 2) isCompact_Icc
  intro t ht
  simp only [etaCircle,Set.indicator_of_notMem ht]

lemma etaCircle_integrable : Integrable etaCircle :=
  etaCircle_continuous.integrable_of_hasCompactSupport etaCircle_hasCompactSupport

lemma etaCircle_square_integrable : Integrable (fun t => etaCircle t ^ 2) := by
  apply (etaCircle_continuous.pow 2).integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (K := Set.Icc (0 : ℝ) 2) isCompact_Icc
  intro t ht
  change etaCircle t ^ 2 = 0
  simp only [etaCircle,Set.indicator_of_notMem ht,zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

lemma etaCircle_deriv_continuous : Continuous (fun t =>
    ((Set.Icc (0 : ℝ) 2).indicator (fun t =>
      -(t-1) * (1-(t-1)^2)^2 * (7-(t-1)^2) * Real.exp (-((t-1)^2)/2)) t)) := by
  apply continuous_indicator
  · intro t ht
    have hb := frontier_subset_closure ht
    rw [isClosed_Icc.closure_eq] at hb
    have hn : t ∉ interior (Set.Icc (0 : ℝ) 2) := ht.2
    rw [interior_Icc] at hn
    have he : t=0 ∨ t=2 := by
      by_contra hh
      apply hn
      have hne0 : t ≠ 0 := by tauto
      have hne2 : t ≠ 2 := by tauto
      exact ⟨lt_of_le_of_ne hb.1 (Ne.symm hne0),lt_of_le_of_ne hb.2 hne2⟩
    rcases he with rfl | rfl <;> norm_num
  · apply Continuous.continuousOn
    fun_prop

lemma etaCircle_deriv_square_integrable : Integrable (fun t =>
    (((Set.Icc (0 : ℝ) 2).indicator (fun t =>
      -(t-1) * (1-(t-1)^2)^2 * (7-(t-1)^2) * Real.exp (-((t-1)^2)/2)) t))^2) := by
  apply (etaCircle_deriv_continuous.pow 2).integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (K := Set.Icc (0 : ℝ) 2) isCompact_Icc
  intro t ht
  change (((Set.Icc (0 : ℝ) 2).indicator (fun t =>
    -(t-1) * (1-(t-1)^2)^2 * (7-(t-1)^2) * Real.exp (-((t-1)^2)/2)) t))^2 = 0
  simp only [Set.indicator_of_notMem ht,zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

end Helfgott
end

section
/-!
A rigorous elementary lower bound for the L² mass of the compact symmetric
smoothing in Helfgott, arXiv:1312.7748v2, (4.3), used in §7.2. The variable
is translated by one: η_circle(t+1) = (1-t²)^3 exp(-t²/2) on [-1,1].
The lower bound 16/25 is derived here using a cubic lower Taylor polynomial
for exp(-u), then exact polynomial integration. Written by Codex.
-/

open MeasureTheory
open scoped Interval

namespace Helfgott

lemma exp_neg_lower_cubic (u : ℝ) (hu : 0 ≤ u) :
    1 - u + u ^ 2 / 2 - u ^ 3 / 6 ≤ Real.exp (-u) := by
  let g₂ : ℝ → ℝ := fun t => 1 - t + t ^ 2 / 2 - Real.exp (-t)
  have hg₂ (t : ℝ) : HasDerivAt g₂ (-1 + t + Real.exp (-t)) t := by
    dsimp [g₂]
    convert! (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).add
      (((hasDerivAt_id t).pow 2).div_const 2)).sub
      (((hasDerivAt_id t).neg).exp) using 1 <;> simp <;> ring
  have hm₂ : Monotone g₂ := monotone_of_hasDerivAt_nonneg hg₂ (by
    intro t
    have ht := Real.add_one_le_exp (-t)
    change 0 ≤ -1 + t + Real.exp (-t)
    linarith)
  have h₂ (t : ℝ) (ht : 0 ≤ t) : 0 ≤ g₂ t := by
    have h := hm₂ ht
    simpa [g₂] using h
  let g₃ : ℝ → ℝ := fun t => Real.exp (-t) - 1 + t - t ^ 2 / 2 + t ^ 3 / 6
  have hg₃ (t : ℝ) : HasDerivAt g₃ (g₂ t) t := by
    dsimp [g₃, g₂]
    convert! (((((((hasDerivAt_id t).neg).exp).sub (hasDerivAt_const t (1 : ℝ))).add
      (hasDerivAt_id t)).sub (((hasDerivAt_id t).pow 2).div_const 2)).add
      (((hasDerivAt_id t).pow 3).div_const 6)) using 1 <;> simp <;> ring
  have hm₃ : MonotoneOn g₃ (Set.Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (by dsimp [g₃]; fun_prop)
      (fun t _ => (hg₃ t).hasDerivWithinAt)
      (fun t ht => h₂ t (Set.mem_Ici.mp (interior_subset ht)))
  have h := hm₃ (by simp : (0 : ℝ) ∈ Set.Ici 0) hu hu
  dsimp [g₃] at h
  norm_num at h
  linarith

theorem symmetric_smoothing_l2_lower :
    (16 / 25 : ℝ) ≤ ∫ t in (-1 : ℝ)..1,
      ((1 - t ^ 2) ^ 3 * Real.exp (-(t ^ 2) / 2)) ^ 2 := by
  let P : ℝ → ℝ := fun t =>
    (1 - t ^ 2) ^ 6 * (1 - t ^ 2 + t ^ 4 / 2 - t ^ 6 / 6)
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
      P t ≤ ((1 - t ^ 2) ^ 3 * Real.exp (-(t ^ 2) / 2)) ^ 2 := by
    have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
    have he := exp_neg_lower_cubic (t ^ 2) ht2
    have hexp : Real.exp (-(t ^ 2) / 2) ^ 2 = Real.exp (-(t ^ 2)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [mul_pow, ← pow_mul, hexp]
    dsimp [P]
    convert! mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ (1 - t ^ 2) ^ 6) using 1 <;>
      (first | rfl | ring | (ext x; ring))
  let Q : ℝ → ℝ := fun t => (1 / 1 : ℝ) * t ^ 1 / 1 + (-7 / 1 : ℝ) * t ^ 3 / 3 + (43 / 2 : ℝ) * t ^ 5 / 5 + (-229 / 6 : ℝ) * t ^ 7 / 7 + (87 / 2 : ℝ) * t ^ 9 / 9 + (-67 / 2 : ℝ) * t ^ 11 / 11 + (107 / 6 : ℝ) * t ^ 13 / 13 + (-13 / 2 : ℝ) * t ^ 15 / 15 + (3 / 2 : ℝ) * t ^ 17 / 17 + (-1 / 6 : ℝ) * t ^ 19 / 19
  have hQ (t : ℝ) : HasDerivAt Q (P t) t := by
    dsimp [Q, P]
    convert! (((((((((((hasDerivAt_const t (0 : ℝ)).add ((((hasDerivAt_id t).pow 1).const_mul (1 / 1 : ℝ)).div_const 1)).add ((((hasDerivAt_id t).pow 3).const_mul (-7 / 1 : ℝ)).div_const 3)).add ((((hasDerivAt_id t).pow 5).const_mul (43 / 2 : ℝ)).div_const 5)).add ((((hasDerivAt_id t).pow 7).const_mul (-229 / 6 : ℝ)).div_const 7)).add ((((hasDerivAt_id t).pow 9).const_mul (87 / 2 : ℝ)).div_const 9)).add ((((hasDerivAt_id t).pow 11).const_mul (-67 / 2 : ℝ)).div_const 11)).add ((((hasDerivAt_id t).pow 13).const_mul (107 / 6 : ℝ)).div_const 13)).add ((((hasDerivAt_id t).pow 15).const_mul (-13 / 2 : ℝ)).div_const 15)).add ((((hasDerivAt_id t).pow 17).const_mul (3 / 2 : ℝ)).div_const 17)).add ((((hasDerivAt_id t).pow 19).const_mul (-1 / 6 : ℝ)).div_const 19)) using 1
    all_goals try funext x
    all_goals simp
    all_goals ring
  have hpint : (∫ t in (-1 : ℝ)..1, P t) = 3104768 / 4849845 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hQ t)
      ((by dsimp [P]; fun_prop : Continuous P).intervalIntegrable _ _)]
    norm_num [Q]
  have hmono : (∫ t in (-1 : ℝ)..1, P t) ≤
      ∫ t in (-1 : ℝ)..1, ((1 - t ^ 2) ^ 3 * Real.exp (-(t ^ 2) / 2)) ^ 2 := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact (by dsimp [P]; fun_prop : Continuous P).intervalIntegrable _ _
    · exact (by fun_prop : Continuous (fun t : ℝ =>
        ((1 - t ^ 2) ^ 3 * Real.exp (-(t ^ 2) / 2)) ^ 2)).intervalIntegrable _ _
    · exact hpoint
  rw [hpint] at hmono
  exact le_trans (by norm_num) hmono

end Helfgott
end

section
/-! An elementary upper bound for the derivative energy of the centered form
of Helfgott's symmetric smoothing (arXiv:1312.7748v2, (4.3), (4.5), (7.6)).
The paper's value is about 2.73753; the bound 17/5 derived here is sufficient
with the sharp polarization constant 1/2. Written by Codex. -/

open MeasureTheory
open scoped Interval

namespace Helfgott

lemma symmetric_smoothing_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s : ℝ => (1-s^2)^3 * Real.exp (-(s^2)/2))
      (-t * (1-t^2)^2 * (7-t^2) * Real.exp (-(t^2)/2)) t := by
  convert! (((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).pow 2)).pow 3).mul
    ((((hasDerivAt_id t).pow 2).neg.div_const 2).exp) using 1 <;> simp <;> ring

theorem symmetric_smoothing_derivative_l2_upper :
    (∫ t in (-1 : ℝ)..1,
      (-t * (1-t^2)^2 * (7-t^2) * Real.exp (-(t^2)/2))^2) ≤ (17/5 : ℝ) := by
  let P : ℝ → ℝ := fun t => t^2 * (1-t^2)^4 * (7-t^2)^2
  have hpoint (t : ℝ) :
      (-t * (1-t^2)^2 * (7-t^2) * Real.exp (-(t^2)/2))^2 ≤ P t := by
    have hexp : Real.exp (-(t^2)/2)^2 = Real.exp (-(t^2)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have he : Real.exp (-(t^2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [sq_nonneg t]
    have h := mul_le_mul_of_nonneg_left he (show 0 ≤ P t by dsimp [P]; positivity)
    convert! h using 1 <;> dsimp [P] <;> simp only [mul_pow, pow_mul, neg_sq, hexp, mul_one] <;> ring
  let Q : ℝ → ℝ := fun t => (49 / 1 : ℝ) * t ^ 3 / 3 + (-210 / 1 : ℝ) * t ^ 5 / 5 + (351 / 1 : ℝ) * t ^ 7 / 7 + (-284 / 1 : ℝ) * t ^ 9 / 9 + (111 / 1 : ℝ) * t ^ 11 / 11 + (-18 / 1 : ℝ) * t ^ 13 / 13 + (1 / 1 : ℝ) * t ^ 15 / 15
  have hQ (t : ℝ) : HasDerivAt Q (P t) t := by
    dsimp [Q,P]
    convert! ((((((((hasDerivAt_const t (0 : ℝ)).add ((((hasDerivAt_id t).pow 3).const_mul (49 / 1 : ℝ)).div_const 3)).add ((((hasDerivAt_id t).pow 5).const_mul (-210 / 1 : ℝ)).div_const 5)).add ((((hasDerivAt_id t).pow 7).const_mul (351 / 1 : ℝ)).div_const 7)).add ((((hasDerivAt_id t).pow 9).const_mul (-284 / 1 : ℝ)).div_const 9)).add ((((hasDerivAt_id t).pow 11).const_mul (111 / 1 : ℝ)).div_const 11)).add ((((hasDerivAt_id t).pow 13).const_mul (-18 / 1 : ℝ)).div_const 13)).add ((((hasDerivAt_id t).pow 15).const_mul (1 / 1 : ℝ)).div_const 15)) using 1
    all_goals try funext x
    all_goals simp
    all_goals ring
  have hpint : (∫ t in (-1 : ℝ)..1, P t) = 152576 / 45045 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hQ t)
      ((by dsimp [P]; fun_prop : Continuous P).intervalIntegrable _ _)]
    norm_num [Q]
  have hmono : (∫ t in (-1 : ℝ)..1,
      (-t * (1-t^2)^2 * (7-t^2) * Real.exp (-(t^2)/2))^2) ≤
      ∫ t in (-1 : ℝ)..1, P t := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact (by fun_prop : Continuous (fun t : ℝ =>
        (-t * (1-t^2)^2 * (7-t^2) * Real.exp (-(t^2)/2))^2)).intervalIntegrable _ _
    · exact (by dsimp [P]; fun_prop : Continuous P).intervalIntegrable _ _
    · intro t _; exact hpoint t
  rw [hpint] at hmono
  exact le_trans hmono (by norm_num)

end Helfgott
end

section
open MeasureTheory Set Filter
open scoped Interval

namespace Helfgott

lemma integral_square_le_length_mul (g : ℝ → ℝ) (hg : Continuous g)
    (h : ℝ) (hh : 0 ≤ h) :
    (∫ t in (0 : ℝ)..h, g t)^2 ≤ h * (∫ t in (0 : ℝ)..h, (g t)^2) := by
  by_cases hz : h=0
  · subst h; simp
  have hp : 0 < h := lt_of_le_of_ne hh (Ne.symm hz)
  let I : ℝ := ∫ t in (0 : ℝ)..h, g t
  let J : ℝ := ∫ t in (0 : ℝ)..h, (g t)^2
  have hn : 0 ≤ ∫ t in (0 : ℝ)..h, (h*g t-I)^2 :=
    intervalIntegral.integral_nonneg hh (fun t _ => sq_nonneg _)
  have heq : (∫ t in (0 : ℝ)..h, (h*g t-I)^2) = h^2*J - (2*h*I)*I + I^2*h := by
    have he (t : ℝ) : (h*g t-I)^2 = h^2*(g t)^2 - (2*h*I)*g t + I^2 := by ring
    simp_rw [he]
    have hi1 : IntervalIntegrable (fun t => h^2*(g t)^2) volume 0 h :=
      (by fun_prop : Continuous (fun t => h^2*(g t)^2)).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun t => (2*h*I)*g t) volume 0 h :=
      (by fun_prop : Continuous (fun t => (2*h*I)*g t)).intervalIntegrable _ _
    rw [intervalIntegral.integral_add (hi1.sub hi2) intervalIntegrable_const,
      intervalIntegral.integral_sub hi1 hi2,
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    dsimp [I,J]
    simp
    ring
  rw [heq] at hn
  have hfac : h^2*J - (2*h*I)*I + I^2*h = h * (h*J-I^2) := by ring
  rw [hfac] at hn
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hn hp)

theorem translation_l2_bound (f g : ℝ → ℝ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g)
    (hg2 : Integrable (fun t => (g t)^2))
    (hder : ∀ t, HasDerivAt f (g t) t) (h : ℝ) (hh : 0 ≤ h) :
    (∫ t : ℝ, (f (t+h)-f t)^2) ≤ h^2 * (∫ t : ℝ, (g t)^2) := by
  have hpoint (t : ℝ) : (f (t+h)-f t)^2 ≤ h * (∫ r in (0 : ℝ)..h, (g (t+r))^2) := by
    have hcon : Continuous (fun r : ℝ => g (t+r)) := by fun_prop
    have hFTC : (∫ r in (0 : ℝ)..h, g (t+r)) = f (t+h)-f t := by
      have hd (r : ℝ) : HasDerivAt (fun r => f (t+r)) (g (t+r)) r := by
        convert! (hder (t+r)).comp r ((hasDerivAt_id r).const_add t) using 1 <;> simp [Function.comp_def]
      simpa only [add_zero] using intervalIntegral.integral_eq_sub_of_hasDerivAt
        (a := (0 : ℝ)) (b := h) (fun r _ => hd r) (hcon.intervalIntegrable _ _)
    rw [← hFTC]
    exact integral_square_le_length_mul _ hcon h hh
  have hpair : Integrable (fun z : ℝ × ℝ => (g (z.2+z.1))^2)
      ((volume.restrict (Set.Ioc (0 : ℝ) h)).prod volume) := by
    apply (integrable_prod_iff (by fun_prop : Continuous (fun z : ℝ × ℝ =>
      (g (z.2+z.1))^2)).aestronglyMeasurable).mpr
    constructor
    · exact Eventually.of_forall (fun r => hg2.comp_add_right r)
    · have heq : (fun r : ℝ => ∫ t : ℝ, ‖(g (t+r))^2‖) =
          fun _ => ∫ t : ℝ, (g t)^2 := by
        funext r
        simp_rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact integral_add_right_eq_self (fun t => (g t)^2) r
      rw [heq]
      exact integrable_const _
  have hdiffc : HasCompactSupport (fun t : ℝ => f (t+h)-f t) := by
    convert! (hfc.comp_isClosedEmbedding (Homeomorph.addRight h).isClosedEmbedding).sub hfc using 1
  have hdiff2 : Integrable (fun t : ℝ => (f (t+h)-f t)^2) := by
    apply (by fun_prop : Continuous (fun t : ℝ => (f (t+h)-f t)^2)).integrable_of_hasCompactSupport
    convert! hdiffc.mul_left (f := fun t => f (t+h)-f t) using 1
    funext t
    simp only [pow_two,Pi.mul_apply]
  have hrhs : Integrable (fun t : ℝ => h * (∫ r in Set.Ioc (0 : ℝ) h, (g (t+r))^2)) :=
    hpair.integral_prod_right.const_mul h
  have hbound : (∫ t : ℝ, (f (t+h)-f t)^2) ≤
      ∫ t : ℝ, h * (∫ r in Set.Ioc (0 : ℝ) h, (g (t+r))^2) := by
    apply integral_mono hdiff2 hrhs
    intro t
    simpa only [intervalIntegral.integral_of_le hh] using hpoint t
  have htotal : (∫ t : ℝ, h * (∫ r in Set.Ioc (0 : ℝ) h, (g (t+r))^2)) =
      h^2 * (∫ t : ℝ, (g t)^2) := by
    rw [integral_const_mul,← integral_integral_swap hpair]
    simp_rw [integral_add_right_eq_self (fun t => (g t)^2)]
    rw [setIntegral_const]
    simp [measureReal_def,Real.volume_Ioc,ENNReal.toReal_ofReal hh]
    ring
  exact hbound.trans_eq htotal

theorem translation_l2_bound_all (f g : ℝ → ℝ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g)
    (hg2 : Integrable (fun t => (g t)^2))
    (hder : ∀ t, HasDerivAt f (g t) t) (h : ℝ) :
    (∫ t : ℝ, (f (t+h)-f t)^2) ≤ h^2 * (∫ t : ℝ, (g t)^2) := by
  by_cases hh : 0 ≤ h
  · exact translation_l2_bound f g hf hfc hg hg2 hder h hh
  · have hh' : 0 ≤ -h := by linarith
    have hb := translation_l2_bound f g hf hfc hg hg2 hder (-h) hh'
    have hi : (∫ t : ℝ, (f (t+h)-f t)^2) = (∫ t : ℝ, (f (t+(-h))-f t)^2) := by
      calc
        (∫ t : ℝ, (f (t+h)-f t)^2) =
            ∫ t : ℝ, (f ((t+h)+(-h))-f (t+h))^2 := by
          apply integral_congr_ae
          exact Eventually.of_forall (fun t => by simp only [add_neg_cancel_right]; ring)
        _ = _ := integral_add_right_eq_self (fun t => (f (t+(-h))-f t)^2) h
    rw [← hi] at hb
    simpa only [neg_sq] using hb

theorem translated_product_lower (f g : ℝ → ℝ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g)
    (hg2 : Integrable (fun t => (g t)^2))
    (hder : ∀ t, HasDerivAt f (g t) t) (h : ℝ) :
    (∫ t : ℝ, (f t)^2) - (h^2/2) * (∫ t : ℝ, (g t)^2) ≤
      ∫ t : ℝ, f t * f (t+h) := by
  have hb := translation_l2_bound_all f g hf hfc hg hg2 hder h
  have hsq : Integrable (fun t : ℝ => (f t)^2) := by
    apply (hf.pow 2).integrable_of_hasCompactSupport
    convert! hfc.mul_left (f := f) using 1
    funext t; simp only [pow_two,Pi.mul_apply]
  have hshift : Integrable (fun t : ℝ => (f (t+h))^2) := hsq.comp_add_right h
  have hp : Integrable (fun t : ℝ => f t * f (t+h)) := by
    apply (by fun_prop : Continuous (fun t : ℝ => f t * f (t+h))).integrable_of_hasCompactSupport
    convert! hfc.mul_right (f' := fun t => f (t+h)) using 1
  have hi : (∫ t : ℝ, (f (t+h)-f t)^2) =
      2*(∫ t : ℝ, (f t)^2) - 2*(∫ t : ℝ, f t * f (t+h)) := by
    calc
      (∫ t : ℝ, (f (t+h)-f t)^2) =
          ∫ t : ℝ, (f (t+h))^2 + (f t)^2 - 2*(f t * f (t+h)) := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun t => by ring)
      _ = _ := by
        rw [integral_sub (f := fun t => (f (t+h))^2 + (f t)^2)
          (g := fun t => 2*(f t * f (t+h))) (hshift.add hsq) (hp.const_mul 2),
          integral_add (f := fun t => (f (t+h))^2) (g := fun t => (f t)^2) hshift hsq,
          integral_const_mul,integral_add_right_eq_self (fun t => (f t)^2)]
        ring
  rw [hi] at hb
  linarith

end Helfgott
end

section
open MeasureTheory Set Filter
open scoped Interval

namespace Helfgott

private noncomputable def circleDeriv (t : ℝ) : ℝ :=
  ((Set.Icc (0 : ℝ) 2).indicator (fun t =>
    -(t-1) * (1-(t-1)^2)^2 * (7-(t-1)^2) * Real.exp (-((t-1)^2)/2)) t)

lemma etaCircle_mass_lower : (16/25 : ℝ) ≤ ∫ t : ℝ, (etaCircle t)^2 := by
  have heq : (∫ t : ℝ, (etaCircle t)^2) =
      ∫ t in (-1 : ℝ)..1, ((1-t^2)^3 * Real.exp (-(t^2)/2))^2 := by
    calc
      (∫ t : ℝ, (etaCircle t)^2) =
          ∫ t : ℝ, (Set.Icc (0 : ℝ) 2).indicator
            (fun t => (t^3*(2-t)^3*Real.exp (-((t-1)^2)/2))^2) t := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun t => by
          by_cases ht : t ∈ Set.Icc (0 : ℝ) 2 <;> simp [etaCircle,ht])
      _ = ∫ t in (0 : ℝ)..2, (t^3*(2-t)^3*Real.exp (-((t-1)^2)/2))^2 := by
        rw [integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
          intervalIntegral.integral_of_le (by norm_num)]
      _ = ∫ t in (-1 : ℝ)..1,
          ((t+1)^3*(2-(t+1))^3*Real.exp (-(((t+1)-1)^2)/2))^2 := by
        simpa only [neg_add_cancel,one_add_one_eq_two] using
          (intervalIntegral.integral_comp_add_right
            (fun t : ℝ => (t^3*(2-t)^3*Real.exp (-((t-1)^2)/2))^2) 1
            (a := (-1 : ℝ)) (b := 1)).symm
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro t _
        simp only [add_sub_cancel_right]
        ring
  rw [heq]
  exact symmetric_smoothing_l2_lower

private lemma circleDeriv_energy_upper : (∫ t : ℝ, (circleDeriv t)^2) ≤ (17/5 : ℝ) := by
  have heq : (∫ t : ℝ, (circleDeriv t)^2) =
      ∫ t in (-1 : ℝ)..1,
        (-t*(1-t^2)^2*(7-t^2)*Real.exp (-(t^2)/2))^2 := by
    calc
      (∫ t : ℝ, (circleDeriv t)^2) =
          ∫ t : ℝ, (Set.Icc (0 : ℝ) 2).indicator
            (fun t => (-(t-1)*(1-(t-1)^2)^2*(7-(t-1)^2)*Real.exp (-((t-1)^2)/2))^2) t := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun t => by
          by_cases ht : t ∈ Set.Icc (0 : ℝ) 2 <;> simp [circleDeriv,ht])
      _ = ∫ t in (0 : ℝ)..2,
          (-(t-1)*(1-(t-1)^2)^2*(7-(t-1)^2)*Real.exp (-((t-1)^2)/2))^2 := by
        rw [integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
          intervalIntegral.integral_of_le (by norm_num)]
      _ = _ := by
        simpa only [neg_add_cancel,one_add_one_eq_two,add_sub_cancel_right] using
          (intervalIntegral.integral_comp_add_right
            (fun t : ℝ => (-(t-1)*(1-(t-1)^2)^2*(7-(t-1)^2)*Real.exp (-((t-1)^2)/2))^2) 1
            (a := (-1 : ℝ)) (b := 1)).symm
  rw [heq]
  exact symmetric_smoothing_derivative_l2_upper

theorem etaCircle_convolution_lower (ρ : ℝ) :
    (16/25 : ℝ) - (17/10 : ℝ)*(ρ-2)^2 ≤
      ∫ t : ℝ, etaCircle t * etaCircle (ρ-t) := by
  have hg : Continuous circleDeriv := etaCircle_deriv_continuous
  have hg2 : Integrable (fun t => (circleDeriv t)^2) := etaCircle_deriv_square_integrable
  have hder (t : ℝ) : HasDerivAt etaCircle (circleDeriv t) t := etaCircle_hasDerivAt t
  have hb := translated_product_lower etaCircle circleDeriv etaCircle_continuous
    etaCircle_hasCompactSupport hg hg2 hder (2-ρ)
  have heq : (∫ t : ℝ, etaCircle t * etaCircle (t+(2-ρ))) =
      ∫ t : ℝ, etaCircle t * etaCircle (ρ-t) := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun t => by
      change etaCircle t * etaCircle (t+(2-ρ)) = etaCircle t * etaCircle (ρ-t)
      rw [← etaCircle_symmetric (ρ-t)]
      congr 2
      ring)
  rw [heq] at hb
  have henergy := circleDeriv_energy_upper
  have hmass := etaCircle_mass_lower
  have hcoef : 0 ≤ (2-ρ)^2/2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left henergy hcoef
  have hs : (2-ρ)^2 = (ρ-2)^2 := by ring
  rw [hs] at hb hmul
  linarith

end Helfgott
end

section
open MeasureTheory Set
open scoped Interval

namespace Helfgott

lemma etaTwo_nonneg (t : ℝ) : 0 ≤ etaTwo t := by
  unfold etaTwo
  split_ifs <;> positivity

lemma etaTwo_le (t : ℝ) : etaTwo t ≤ 4 * Real.log 2 := by
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  unfold etaTwo
  split_ifs
  · apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact max_le (sub_le_self _ (abs_nonneg _)) hlog
  · positivity

lemma etaTwo_eq_zero_of_not_mem (t : ℝ) (ht : t ∉ Set.Icc (1/4 : ℝ) 1) :
    etaTwo t = 0 := by
  by_cases hpos : 0 < t
  · unfold etaTwo
    rw [if_pos hpos]
    have htwopos : 0 < 2*t := by positivity
    have hm : Real.log 2 - |Real.log (2*t)| ≤ 0 := by
      rcases (not_and_or.mp ht) with hlo | hhi
      · have hlt : 2*t ≤ (1/2 : ℝ) := by push_neg at hlo; linarith
        have hlog := Real.log_le_log htwopos hlt
        have hhalf : Real.log (1/2 : ℝ) = -Real.log 2 := by
          rw [one_div, Real.log_inv]
        rw [hhalf] at hlog
        linarith [neg_le_abs (Real.log (2*t))]
      · have hlt : (2 : ℝ) ≤ 2*t := by push_neg at hhi; linarith
        have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hlt
        linarith [le_abs_self (Real.log (2*t))]
    rw [max_eq_right hm, mul_zero]
  · simp [etaTwo,hpos]

lemma etaTwo_eq_lower (t : ℝ) (ht : t ∈ Set.Icc (1/4 : ℝ) (1/2)) :
    etaTwo t = 4 * Real.log (4*t) := by
  have hpos : 0 < t := by linarith [ht.1]
  have hprod : 0 < 2*t := by positivity
  have hlogneg : Real.log (2*t) ≤ 0 := Real.log_nonpos (le_of_lt hprod) (by linarith [ht.2])
  have hsum : Real.log 2 + Real.log (2*t) = Real.log (4*t) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hprod)]
    congr 1; ring
  have hn : 0 ≤ Real.log (4*t) := Real.log_nonneg (by linarith [ht.1])
  unfold etaTwo
  rw [if_pos hpos, abs_of_nonpos hlogneg, sub_neg_eq_add, hsum, max_eq_left hn]

lemma etaTwo_eq_upper (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1) :
    etaTwo t = -4 * Real.log t := by
  have hpos : 0 < t := by linarith [ht.1]
  have hlogpos : 0 ≤ Real.log (2*t) := Real.log_nonneg (by linarith [ht.1])
  have hlogneg : Real.log t ≤ 0 := Real.log_nonpos (le_of_lt hpos) ht.2
  have hlog : Real.log (2*t) = Real.log 2 + Real.log t :=
    Real.log_mul (by norm_num) (ne_of_gt hpos)
  unfold etaTwo
  rw [if_pos hpos, abs_of_nonneg hlogpos, hlog]
  have hm : Real.log 2 - (Real.log 2 + Real.log t) = -Real.log t := by ring
  rw [hm, max_eq_left (neg_nonneg.mpr hlogneg)]
  ring

lemma etaTwo_continuousOn_pos : ContinuousOn etaTwo (Set.Ioi (0 : ℝ)) := by
  intro t ht
  apply ContinuousAt.continuousWithinAt
  have hg : ContinuousAt (fun s : ℝ => 4 * max (Real.log 2 - |Real.log (2*s)|) 0) t := by
    have hpos : 0 < t := ht
    have hn : 2*t ≠ 0 := by positivity
    fun_prop
  apply hg.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with x hx
  simp only [etaTwo, if_pos (show 0 < x from hx)]

theorem etaTwo_mass_interval : (∫ t in (1/4 : ℝ)..1, etaTwo t) = 1 := by
  have hint (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : IntervalIntegrable etaTwo volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply etaTwo_continuousOn_pos.mono
    intro t ht
    exact lt_of_lt_of_le (lt_min ha hb) ht.1
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hint (1/4) (1/2) (by norm_num) (by norm_num))
    (hint (1/2) 1 (by norm_num) (by norm_num))]
  have hlo : (∫ t in (1/4 : ℝ)..(1/2), etaTwo t) =
      ∫ t in (1/4 : ℝ)..(1/2), 4 * (Real.log 4 + Real.log t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have hmem : t ∈ Set.Icc (1/4 : ℝ) (1/2) := by
      have h := Set.uIcc_of_le (by norm_num : (1/4 : ℝ) ≤ 1/2)
      rw [h] at ht
      exact ht
    rw [etaTwo_eq_lower t hmem, Real.log_mul (by norm_num) (by linarith [hmem.1] : t ≠ 0)]
  have hhi : (∫ t in (1/2 : ℝ)..1, etaTwo t) = ∫ t in (1/2 : ℝ)..1, -4 * Real.log t := by
    apply intervalIntegral.integral_congr
    intro t ht
    apply etaTwo_eq_upper
    rw [Set.uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 1)] at ht
    exact ht
  rw [hlo,hhi,intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (intervalIntegrable_const) (intervalIntegral.intervalIntegrable_log'),
    intervalIntegral.integral_const,integral_log,integral_log]
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  have hhalf : Real.log (1/2 : ℝ) = -Real.log 2 := by rw [one_div,Real.log_inv]
  have hquarter : Real.log (1/4 : ℝ) = -(2 * Real.log 2) := by rw [one_div,Real.log_inv,h4]
  rw [h4,hhalf,hquarter,Real.log_one]
  norm_num
  ring

lemma etaTwo_continuous : Continuous etaTwo := by
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : 0 < t
  · exact (etaTwo_continuousOn_pos t ht).continuousAt (Ioi_mem_nhds ht)
  · have hlo : t < (1/4 : ℝ) := by linarith
    apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hlo] with x hx
    apply etaTwo_eq_zero_of_not_mem
    intro h; exact (not_lt_of_ge h.1) hx

lemma etaTwo_hasCompactSupport : HasCompactSupport etaTwo := by
  apply HasCompactSupport.intro (K := Set.Icc (1/4 : ℝ) 1) isCompact_Icc
  exact etaTwo_eq_zero_of_not_mem

lemma etaTwo_integrable : Integrable etaTwo :=
  etaTwo_continuous.integrable_of_hasCompactSupport etaTwo_hasCompactSupport

theorem etaTwo_mass : (∫ t : ℝ, etaTwo t) = 1 := by
  have hind : (Set.Icc (1/4 : ℝ) 1).indicator etaTwo = etaTwo := by
    funext t
    by_cases ht : t ∈ Set.Icc (1/4 : ℝ) 1
    · exact Set.indicator_of_mem ht etaTwo
    · rw [Set.indicator_of_notMem ht,etaTwo_eq_zero_of_not_mem t ht]
  calc
    (∫ t : ℝ, etaTwo t) = ∫ t : ℝ, (Set.Icc (1/4 : ℝ) 1).indicator etaTwo t := by rw [hind]
    _ = ∫ t in Set.Icc (1/4 : ℝ) 1, etaTwo t := integral_indicator measurableSet_Icc
    _ = ∫ t in (1/4 : ℝ)..1, etaTwo t := by
      rw [intervalIntegral.integral_of_le (by norm_num),integral_Icc_eq_integral_Ioc]
    _ = 1 := etaTwo_mass_interval

end Helfgott
end

section
open MeasureTheory Set
open scoped Interval

namespace Helfgott

lemma etaTwo_scaled_zero (T w : ℝ) (hT : 0 < T) (hw : w ∉ Icc T (4*T)) :
    etaTwo (T/w) = 0 := by
  by_cases hwp : 0 < w
  · apply etaTwo_eq_zero_of_not_mem
    intro h
    apply hw
    constructor
    · simpa using (div_le_iff₀ hwp).mp h.2
    · have hh := (le_div_iff₀ hwp).mp h.1
      nlinarith
  · have hh : T/w ≤ 0 := div_nonpos_of_nonneg_of_nonpos hT.le (le_of_not_gt hwp)
    simp [etaTwo, not_lt_of_ge hh]

lemma etaTwo_scaled_weight_continuous (T : ℝ) (hT : 0 < T) :
    Continuous (fun w : ℝ => etaTwo (T/w)/w) := by
  apply continuous_iff_continuousAt.mpr
  intro w
  by_cases hw : w = 0
  · subst w
    apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hT] with x hx
    change x < T at hx
    rw [etaTwo_scaled_zero T x hT (by intro hm; linarith [hm.1]), zero_div]
  · have hc : ContinuousAt (fun x : ℝ => T/x) w := by fun_prop
    exact (etaTwo_continuous.continuousAt.comp hc).div continuousAt_id hw

lemma etaTwo_scaled_weight_integrable (T : ℝ) (hT : 0 < T) :
    Integrable (fun w : ℝ => etaTwo (T/w)/w) := by
  apply (etaTwo_scaled_weight_continuous T hT).integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (K := Icc T (4*T)) isCompact_Icc
  intro w hw
  rw [etaTwo_scaled_zero T w hT hw,zero_div]

lemma etaTwo_scaled_lower (T w : ℝ) (hT : 0 < T) (hw : w ∈ Icc T (2*T)) :
    etaTwo (T/w) = 4 * (Real.log w - Real.log T) := by
  have hwp : 0 < w := lt_of_lt_of_le hT hw.1
  have hm : T/w ∈ Icc (1/2 : ℝ) 1 := by
    constructor
    · apply (le_div_iff₀ hwp).mpr; linarith [hw.2]
    · apply (div_le_iff₀ hwp).mpr; simpa using hw.1
  rw [etaTwo_eq_upper _ hm, Real.log_div hT.ne' hwp.ne']
  ring

lemma etaTwo_scaled_upper (T w : ℝ) (hT : 0 < T) (hw : w ∈ Icc (2*T) (4*T)) :
    etaTwo (T/w) = 4 * (Real.log (4*T) - Real.log w) := by
  have hwp : 0 < w := by linarith [hw.1]
  have hm : T/w ∈ Icc (1/4 : ℝ) (1/2) := by
    constructor
    · apply (le_div_iff₀ hwp).mpr; linarith [hw.2]
    · apply (div_le_iff₀ hwp).mpr; linarith [hw.1]
  rw [etaTwo_eq_lower _ hm]
  rw [show 4*(T/w) = (4*T)/w by ring,
    Real.log_div (by positivity : 4*T ≠ 0) hwp.ne']

theorem etaTwo_scaled_log_mass (T : ℝ) (hT : 0 < T) :
    (∫ w in Ioi (0 : ℝ), etaTwo (T/w)/w) = 4 * (Real.log 2)^2 := by
  have hf := etaTwo_scaled_weight_continuous T hT
  have hi (a b : ℝ) : IntervalIntegrable (fun w => etaTwo (T/w)/w) volume a b :=
    hf.intervalIntegrable _ _
  have hrestrict : (∫ w in Ioi (0 : ℝ), etaTwo (T/w)/w) =
      ∫ w in T..4*T, etaTwo (T/w)/w := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (show Icc T (4*T) ⊆ Ioi (0 : ℝ) by intro w hw; exact lt_of_lt_of_le hT hw.1)
      (show ∀ w ∈ Ioi (0 : ℝ) \ Icc T (4*T), etaTwo (T/w)/w = 0 by
        intro w hw; rw [etaTwo_scaled_zero T w hT hw.2,zero_div])]
    rw [intervalIntegral.integral_of_le (by linarith),integral_Icc_eq_integral_Ioc]
  rw [hrestrict, ← intervalIntegral.integral_add_adjacent_intervals (hi T (2*T)) (hi (2*T) (4*T))]
  have hlo : (∫ w in T..2*T, etaTwo (T/w)/w) =
      2*(Real.log (2*T)-Real.log T)^2 := by
    have heq : (∫ w in T..2*T, etaTwo (T/w)/w) =
        ∫ w in T..2*T, 4*(Real.log w-Real.log T)/w := by
      apply intervalIntegral.integral_congr
      intro w hw
      rw [Set.uIcc_of_le (by linarith : T ≤ 2*T)] at hw
      dsimp only
      rw [etaTwo_scaled_lower T w hT hw]
    rw [heq]
    have hint : IntervalIntegrable (fun w : ℝ => 4*(Real.log w-Real.log T)/w)
        volume T (2*T) := by
      apply ContinuousOn.intervalIntegrable
      intro w hw
      have hwp : 0 < w := by
        rw [Set.uIcc_of_le (by linarith : T ≤ 2*T)] at hw
        linarith [hw.1]
      apply ContinuousAt.continuousWithinAt
      have hwn : w ≠ 0 := hwp.ne'
      fun_prop
    have hd (w : ℝ) (hw : w ∈ uIcc T (2*T)) :
        HasDerivAt (fun w : ℝ => 2*(Real.log w-Real.log T)^2)
          (4*(Real.log w-Real.log T)/w) w := by
      rw [Set.uIcc_of_le (by linarith : T ≤ 2*T)] at hw
      have hwp : 0 < w := by linarith [hw.1]
      convert! (((Real.hasDerivAt_log hwp.ne').sub_const (Real.log T)).pow 2).const_mul 2 using 1 <;> simp <;> ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
    simp
  have hhi : (∫ w in 2*T..4*T, etaTwo (T/w)/w) =
      2*(Real.log (4*T)-Real.log (2*T))^2 := by
    have heq : (∫ w in 2*T..4*T, etaTwo (T/w)/w) =
        ∫ w in 2*T..4*T, 4*(Real.log (4*T)-Real.log w)/w := by
      apply intervalIntegral.integral_congr
      intro w hw
      rw [Set.uIcc_of_le (by linarith : 2*T ≤ 4*T)] at hw
      dsimp only
      rw [etaTwo_scaled_upper T w hT hw]
    rw [heq]
    have hint : IntervalIntegrable (fun w : ℝ => 4*(Real.log (4*T)-Real.log w)/w)
        volume (2*T) (4*T) := by
      apply ContinuousOn.intervalIntegrable
      intro w hw
      have hwp : 0 < w := by
        rw [Set.uIcc_of_le (by linarith : 2*T ≤ 4*T)] at hw
        linarith [hw.1]
      apply ContinuousAt.continuousWithinAt
      have hwn : w ≠ 0 := hwp.ne'
      fun_prop
    have hd (w : ℝ) (hw : w ∈ uIcc (2*T) (4*T)) :
        HasDerivAt (fun w : ℝ => -2*(Real.log (4*T)-Real.log w)^2)
          (4*(Real.log (4*T)-Real.log w)/w) w := by
      rw [Set.uIcc_of_le (by linarith : 2*T ≤ 4*T)] at hw
      have hwp : 0 < w := by linarith [hw.1]
      convert! (((Real.hasDerivAt_log hwp.ne').const_sub (Real.log (4*T))).pow 2).const_mul (-2) using 1 <;> simp <;> ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
    simp
  rw [hlo,hhi,Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hT.ne',
    Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hT.ne']
  have h4 : Real.log (4 : ℝ) = 2*Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  rw [h4]
  ring

lemma phi_nonneg (t : ℝ) : 0 ≤ phi t := by unfold phi; positivity

lemma phi_le (t : ℝ) : phi t ≤ 2 / Real.exp 1 := by
  have h := Real.mul_exp_neg_le_exp_neg_one (t^2/2)
  have he : Real.exp (-1 : ℝ) = (Real.exp 1)⁻¹ := Real.exp_neg 1
  rw [he] at h
  unfold phi
  have heq : -(t^2/2) = -(t^2)/2 := by ring
  rw [heq] at h
  calc
    t^2*Real.exp (-(t^2)/2) = 2*((t^2/2)*Real.exp (-(t^2)/2)) := by ring
    _ ≤ 2*(Real.exp 1)⁻¹ := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = 2/Real.exp 1 := by ring

lemma mellin_etaTwo_phi_integrable (T : ℝ) (hT : 0 < T) :
    Integrable (fun w : ℝ => etaTwo (T/w)*phi w/w) := by
  have hphi : Continuous phi := by unfold phi; fun_prop
  have hc : Continuous (fun w : ℝ => (etaTwo (T/w)/w)*phi w) :=
    (etaTwo_scaled_weight_continuous T hT).mul hphi
  have hs : HasCompactSupport (fun w : ℝ => (etaTwo (T/w)/w)*phi w) := by
    apply HasCompactSupport.intro (K := Icc T (4*T)) isCompact_Icc
    intro w hw
    rw [etaTwo_scaled_zero T w hT hw,zero_div,zero_mul]
  have hh : Integrable (fun w : ℝ => (etaTwo (T/w)/w)*phi w) := hc.integrable_of_hasCompactSupport hs
  have heq : (fun w : ℝ => etaTwo (T/w)*phi w/w) = (fun w : ℝ => (etaTwo (T/w)/w)*phi w) := by
    funext w; ring
  rw [heq]
  exact hh

lemma mellin_etaTwo_phi_nonneg (T : ℝ) : 0 ≤ mellinConv etaTwo phi T := by
  unfold mellinConv
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
  exact div_nonneg (mul_nonneg (etaTwo_nonneg _) (phi_nonneg _)) (le_of_lt hw)

lemma mellin_etaTwo_phi_le (T : ℝ) :
    mellinConv etaTwo phi T ≤ 8*(Real.log 2)^2/Real.exp 1 := by
  by_cases hT : 0 < T
  · have hi := (mellin_etaTwo_phi_integrable T hT).restrict (s := Ioi (0 : ℝ))
    have hg := ((etaTwo_scaled_weight_integrable T hT).const_mul (2/Real.exp 1)).restrict
      (s := Ioi (0 : ℝ))
    have hbound : (∫ w in Ioi (0 : ℝ), etaTwo (T/w)*phi w/w) ≤
        ∫ w in Ioi (0 : ℝ), (2/Real.exp 1)*(etaTwo (T/w)/w) := by
      apply integral_mono_ae hi hg
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
      have he := mul_le_mul_of_nonneg_left (phi_le w) (etaTwo_nonneg (T/w))
      have hh := div_le_div_of_nonneg_right he (le_of_lt hw)
      convert! hh using 1 <;> ring
    unfold mellinConv
    refine hbound.trans_eq ?_
    rw [integral_const_mul,etaTwo_scaled_log_mass T hT]
    ring
  · have hz : mellinConv etaTwo phi T = 0 := by
      unfold mellinConv
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
      have hh : T/w ≤ 0 := div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hT) (le_of_lt hw)
      simp [etaTwo,not_lt_of_ge hh]
    rw [hz]
    positivity

lemma mellin_etaTwo_phi_le_rational (T : ℝ) :
    mellinConv etaTwo phi T ≤ (707/500 : ℝ) := by
  apply (mellin_etaTwo_phi_le T).trans
  apply (div_le_iff₀ (Real.exp_pos 1)).mpr
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hs : (Real.log 2)^2 ≤ (0.6931471808 : ℝ)^2 :=
    pow_le_pow_left₀ hlog Real.log_two_lt_d9.le 2
  nlinarith only [hs, Real.exp_one_gt_d9]

theorem etaStar_abs_le (t : ℝ) : |etaStar t| ≤ (707/500 : ℝ) := by
  unfold etaStar
  rw [abs_of_nonneg (mellin_etaTwo_phi_nonneg (49*t))]
  exact mellin_etaTwo_phi_le_rational (49*t)

end Helfgott
end

section
open MeasureTheory Set Filter

namespace Helfgott

lemma mellin_inner_integrable (f : ℝ → ℝ) (hf : IntegrableOn f (Ioi (0 : ℝ)))
    (w c : ℝ) (hw : 0 < w) :
    IntegrableOn (fun t : ℝ => f (t/w)*c/w) (Ioi (0 : ℝ)) := by
  have hh : IntegrableOn (fun t : ℝ => f (t*w⁻¹)) (Ioi (0 : ℝ)) := by
    apply (integrableOn_Ioi_comp_mul_right_iff f 0 (inv_pos.mpr hw)).mpr
    simpa using hf
  simpa only [IntegrableOn,div_eq_mul_inv,mul_assoc] using (hh.mul_const c).mul_const w⁻¹

lemma mellin_inner_integral (f : ℝ → ℝ) (w c : ℝ) (hw : 0 < w) :
    (∫ t in Ioi (0 : ℝ), f (t/w)*c/w) = c*(∫ t in Ioi (0 : ℝ), f t) := by
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const,integral_mul_const,
    integral_comp_mul_right_Ioi f 0 (inv_pos.mpr hw)]
  simp only [zero_mul,inv_inv,smul_eq_mul]
  field_simp

theorem mellin_integrable_mass (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfi : IntegrableOn f (Ioi (0 : ℝ))) (hgi : IntegrableOn g (Ioi (0 : ℝ)))
    (hfn : ∀ t, 0 < t → 0 ≤ f t) (hgn : ∀ t, 0 < t → 0 ≤ g t) :
    IntegrableOn (mellinConv f g) (Ioi (0 : ℝ)) ∧
    (∫ t in Ioi (0 : ℝ), mellinConv f g t) =
      (∫ t in Ioi (0 : ℝ), f t)*(∫ t in Ioi (0 : ℝ), g t) := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hm : Measurable (fun z : ℝ × ℝ => f (z.2/z.1)*g z.1/z.1) := by
    fun_prop
  have hp : Integrable (fun z : ℝ × ℝ => f (z.2/z.1)*g z.1/z.1) (μ.prod μ) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
      exact mellin_inner_integrable f hfi w (g w) hw
    · have heq : (fun w : ℝ => ∫ t, ‖f (t/w)*g w/w‖ ∂μ) =ᵐ[μ]
          fun w => g w*(∫ t, f t ∂μ) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
        have hnorm : (∫ t, ‖f (t/w)*g w/w‖ ∂μ) = ∫ t, f (t/w)*g w/w ∂μ := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact Real.norm_of_nonneg
            (div_nonneg (mul_nonneg (hfn _ (div_pos ht hw)) (hgn _ hw)) hw.le)
        rw [hnorm]
        exact mellin_inner_integral f w (g w) hw
      apply (hgi.mul_const (∫ t, f t ∂μ)).congr
      exact heq.symm
  constructor
  · exact hp.integral_prod_right
  unfold mellinConv
  change (∫ t, ∫ w, f (t/w)*g w/w ∂μ ∂μ) = _
  rw [← integral_integral_swap hp]
  have heq : (∫ w, ∫ t, f (t/w)*g w/w ∂μ ∂μ) =
      ∫ w, g w*(∫ t, f t ∂μ) ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    exact mellin_inner_integral f w (g w) hw
  rw [heq,integral_mul_const]
  exact mul_comm _ _

lemma mellin_moment_identity (f g : ℝ → ℝ) (k : ℕ) (t : ℝ) :
    t^k*mellinConv f g t =
      mellinConv (fun t => t^k*f t) (fun w => w^k*g w) t := by
  unfold mellinConv
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
  rw [div_pow]
  have hn : w ≠ 0 := hw.ne'
  field_simp

theorem mellin_moment (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (k : ℕ) (hfi : IntegrableOn (fun t => t^k*f t) (Ioi (0 : ℝ)))
    (hgi : IntegrableOn (fun t => t^k*g t) (Ioi (0 : ℝ)))
    (hfn : ∀ t, 0 < t → 0 ≤ f t) (hgn : ∀ t, 0 < t → 0 ≤ g t) :
    IntegrableOn (fun t => t^k*mellinConv f g t) (Ioi (0 : ℝ)) ∧
    (∫ t in Ioi (0 : ℝ), t^k*mellinConv f g t) =
      (∫ t in Ioi (0 : ℝ), t^k*f t)*(∫ t in Ioi (0 : ℝ), t^k*g t) := by
  simp_rw [mellin_moment_identity]
  apply mellin_integrable_mass _ _ ((continuous_id.pow k).mul hf) ((continuous_id.pow k).mul hg)
    hfi hgi
  · intro t ht; exact mul_nonneg (pow_nonneg ht.le k) (hfn t ht)
  · intro t ht; exact mul_nonneg (pow_nonneg ht.le k) (hgn t ht)

end Helfgott
end

section
open MeasureTheory Set
open scoped Interval

namespace Helfgott

lemma integral_power_log (k : ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (C : ℝ) :
    (∫ t in a..b, t^k*(C+Real.log t)) =
      b^(k+1)/((k:ℝ)+1)*(C+Real.log b-1/((k:ℝ)+1)) -
      a^(k+1)/((k:ℝ)+1)*(C+Real.log a-1/((k:ℝ)+1)) := by
  have hkn : (k:ℝ)+1 ≠ 0 := by have hk := Nat.cast_nonneg (α := ℝ) k; linarith
  have hpos (t : ℝ) (ht : t ∈ uIcc a b) : 0 < t := lt_of_lt_of_le (lt_min ha hb) ht.1
  have hi : IntervalIntegrable (fun t : ℝ => t^k*(C+Real.log t)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have hn : t ≠ 0 := (hpos t ht).ne'
    apply ContinuousAt.continuousWithinAt
    fun_prop
  have hd (t : ℝ) (ht : t ∈ uIcc a b) :
      HasDerivAt (fun t : ℝ => t^(k+1)/((k:ℝ)+1)*(C+Real.log t-1/((k:ℝ)+1)))
        (t^k*(C+Real.log t)) t := by
    have hn : t ≠ 0 := (hpos t ht).ne'
    have hp := ((hasDerivAt_id t).pow (k+1)).div_const ((k:ℝ)+1)
    have hl := ((Real.hasDerivAt_log hn).const_add C).sub_const (1/((k:ℝ)+1))
    convert! hp.mul hl using 1
    all_goals simp only [Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel,one_mul,id_eq,Pi.pow_apply]
    all_goals field_simp
    all_goals simp only [pow_succ]
    all_goals ring
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi

lemma etaTwo_moment_integrable (k : ℕ) : Integrable (fun t : ℝ => t^k*etaTwo t) := by
  apply ((continuous_id.pow k).mul etaTwo_continuous).integrable_of_hasCompactSupport
  exact etaTwo_hasCompactSupport.mul_left

lemma etaTwo_moment_formula (k : ℕ) :
    (∫ t : ℝ, t^k*etaTwo t) =
      4*((1/2:ℝ)^(k+1)/((k:ℝ)+1)*(Real.log 4+Real.log (1/2)-1/((k:ℝ)+1)) -
        (1/4:ℝ)^(k+1)/((k:ℝ)+1)*(Real.log 4+Real.log (1/4)-1/((k:ℝ)+1))) -
      4*(1/((k:ℝ)+1)*(Real.log 1-1/((k:ℝ)+1)) -
        (1/2:ℝ)^(k+1)/((k:ℝ)+1)*(Real.log (1/2)-1/((k:ℝ)+1))) := by
  have hc : Continuous (fun t : ℝ => t^k*etaTwo t) := (continuous_id.pow k).mul etaTwo_continuous
  have heq : (∫ t : ℝ, t^k*etaTwo t) = ∫ t in (1/4:ℝ)..1, t^k*etaTwo t := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (1/4:ℝ) 1)
      (show ∀ t : ℝ, t ∉ Icc (1/4:ℝ) 1 → t^k*etaTwo t = 0 by
        intro t ht; rw [etaTwo_eq_zero_of_not_mem t ht,mul_zero])]
    rw [intervalIntegral.integral_of_le (by norm_num),integral_Icc_eq_integral_Ioc]
  rw [heq, ← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (1/4) (1/2)) (hc.intervalIntegrable (1/2) 1)]
  have hlo : (∫ t in (1/4:ℝ)..(1/2), t^k*etaTwo t) =
      4*∫ t in (1/4:ℝ)..(1/2), t^k*(Real.log 4+Real.log t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (1/4:ℝ) ≤ 1/2)] at ht
    dsimp only
    rw [etaTwo_eq_lower t ht,Real.log_mul (by norm_num) (by linarith [ht.1] : t ≠ 0)]
    ring
  have hhi : (∫ t in (1/2:ℝ)..1, t^k*etaTwo t) =
      -4*∫ t in (1/2:ℝ)..1, t^k*(0+Real.log t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 1)] at ht
    dsimp only
    rw [etaTwo_eq_upper t ht]
    ring
  rw [hlo,hhi,integral_power_log k (1/4) (1/2) (by norm_num) (by norm_num) (Real.log 4),
    integral_power_log k (1/2) 1 (by norm_num) (by norm_num) 0]
  simp
  ring

theorem etaTwo_first_moment : (∫ t : ℝ, t*etaTwo t) = (9/16 : ℝ) := by
  have h := etaTwo_moment_formula 1
  have heq : (fun t : ℝ => t*etaTwo t) = fun t => t^1*etaTwo t := by simp
  rw [heq,h]
  have h4 : Real.log (4 : ℝ) = 2*Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num,Real.log_pow]; norm_num
  have hh : Real.log (1/2 : ℝ) = -Real.log 2 := by rw [one_div,Real.log_inv]
  have hq : Real.log (1/4 : ℝ) = -(2*Real.log 2) := by rw [one_div,Real.log_inv,h4]
  rw [hh,hq,h4,Real.log_one]
  norm_num
  ring

theorem etaTwo_second_moment : (∫ t : ℝ, t^2*etaTwo t) = (49/144 : ℝ) := by
  rw [etaTwo_moment_formula 2]
  have h4 : Real.log (4 : ℝ) = 2*Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num,Real.log_pow]; norm_num
  have hh : Real.log (1/2 : ℝ) = -Real.log 2 := by rw [one_div,Real.log_inv]
  have hq : Real.log (1/4 : ℝ) = -(2*Real.log 2) := by rw [one_div,Real.log_inv,h4]
  rw [hh,hq,h4,Real.log_one]
  norm_num
  ring

end Helfgott
end

section
open MeasureTheory Set

namespace Helfgott

lemma phi_moment_integrable (k : ℕ) :
    IntegrableOn (fun t : ℝ => t^k*phi t) (Ioi (0 : ℝ)) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2)
    (s := ((k+2 : ℕ) : ℝ)) (by have hk := Nat.cast_nonneg (α := ℝ) (k+2); linarith : (-1 : ℝ) < ((k+2 : ℕ) : ℝ))
  convert! h using 1
  funext t
  rw [Real.rpow_natCast]
  unfold phi
  rw [pow_add]
  have he : -(1/2 : ℝ)*t^2 = -(t^2)/2 := by ring
  rw [he]
  ring

lemma gaussian_power_integral (k : ℕ) :
    (∫ t in Ioi (0 : ℝ), t^k*Real.exp (-(t^2)/2)) =
      (1/2 : ℝ)^(-(((k : ℝ)+1)/2))*(1/2)*Real.Gamma (((k : ℝ)+1)/2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow
    (p := (2 : ℝ)) (q := (k : ℝ)) (b := (1/2 : ℝ))
    (by norm_num) (by have hk := Nat.cast_nonneg (α := ℝ) k; linarith) (by norm_num)
  simp only [neg_div] at h ⊢
  rw [← h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [Real.rpow_natCast,Real.rpow_two]
  congr 1 <;> ring

theorem phi_mass : (∫ t in Ioi (0 : ℝ), phi t) = Real.sqrt (Real.pi/2) := by
  have h := gaussian_power_integral 2
  norm_num only [Nat.cast_ofNat] at h
  have hg : Real.Gamma (3/2 : ℝ) = (1/2)*Real.sqrt Real.pi := by
    rw [show (3/2 : ℝ) = 1/2+1 by norm_num,
      Real.Gamma_add_one (by norm_num),Real.Gamma_one_half_eq]
  have he : (1/2 : ℝ)^(-(3/2 : ℝ)) = 2*Real.sqrt 2 := by
    rw [show (-(3/2 : ℝ)) = -1+ -(1/2 : ℝ) by norm_num,
      Real.rpow_add (by norm_num : (0 : ℝ) < 1/2),Real.rpow_neg_one,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1/2),← Real.sqrt_eq_rpow]
    norm_num
  change (∫ t in Ioi (0 : ℝ), t^2*Real.exp (-(t^2)/2)) = _
  rw [h]
  norm_num
  rw [hg,he]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  field_simp
  nlinarith

theorem phi_first_moment : (∫ t in Ioi (0 : ℝ), t*phi t) = 2 := by
  have h := gaussian_power_integral 3
  have hg : Real.Gamma (2 : ℝ) = 1 := by
    rw [show (2 : ℝ) = 1+1 by norm_num,Real.Gamma_add_one (by norm_num),Real.Gamma_one]
    norm_num
  have he : (1/2 : ℝ)^(-(2 : ℝ)) = 4 := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1/2),Real.rpow_two]
    norm_num
  have heq : (fun t : ℝ => t*phi t) = fun t => t^3*Real.exp (-(t^2)/2) := by
    funext t; unfold phi; ring
  rw [heq,h]
  norm_num [hg,he]

theorem phi_second_moment : (∫ t in Ioi (0 : ℝ), t^2*phi t) =
    3*Real.sqrt (Real.pi/2) := by
  have h := gaussian_power_integral 4
  have hg : Real.Gamma (5/2 : ℝ) = (3/4)*Real.sqrt Real.pi := by
    rw [show (5/2 : ℝ) = 3/2+1 by norm_num,Real.Gamma_add_one (by norm_num),
      show (3/2 : ℝ) = 1/2+1 by norm_num,Real.Gamma_add_one (by norm_num),Real.Gamma_one_half_eq]
    ring
  have he : (1/2 : ℝ)^(-(5/2 : ℝ)) = 4*Real.sqrt 2 := by
    rw [show (-(5/2 : ℝ)) = -2+ -(1/2 : ℝ) by norm_num,
      Real.rpow_add (by norm_num : (0 : ℝ) < 1/2),Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1/2),
      Real.rpow_two,Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1/2),← Real.sqrt_eq_rpow]
    norm_num
  have heq : (fun t : ℝ => t^2*phi t) = fun t => t^4*Real.exp (-(t^2)/2) := by
    funext t; unfold phi; ring
  rw [heq,h]
  norm_num
  rw [hg,he]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  field_simp
  nlinarith

end Helfgott
end

section
open MeasureTheory Set

namespace Helfgott

lemma etaTwo_moment_pos_integral (k : ℕ) :
    (∫ t in Ioi (0 : ℝ), t^k*etaTwo t) = ∫ t : ℝ, t^k*etaTwo t := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  simp [etaTwo,show ¬0 < t from ht]

lemma mellin_etaTwo_phi_moment (k : ℕ) :
    IntegrableOn (fun t => t^k*mellinConv etaTwo phi t) (Ioi (0 : ℝ)) ∧
    (∫ t in Ioi (0 : ℝ), t^k*mellinConv etaTwo phi t) =
      (∫ t : ℝ, t^k*etaTwo t)*(∫ t in Ioi (0 : ℝ), t^k*phi t) := by
  rw [← etaTwo_moment_pos_integral]
  apply mellin_moment _ _ etaTwo_continuous (by unfold phi; fun_prop)
    k (etaTwo_moment_integrable k).integrableOn (phi_moment_integrable k)
  · intro t ht; exact etaTwo_nonneg t
  · intro t ht; unfold phi; positivity

lemma scaled_moment_integral (F : ℝ → ℝ) (κ : ℝ) (hκ : 0 < κ) (k : ℕ) :
    (∫ t in Ioi (0 : ℝ), t^k*F (κ*t)) =
      (∫ t in Ioi (0 : ℝ), t^k*F t)/κ^(k+1) := by
  have heq : (fun t : ℝ => t^k*F (κ*t)) =
      fun t => (κ^k)⁻¹*((κ*t)^k*F (κ*t)) := by
    funext t
    rw [mul_pow]
    field_simp
  rw [heq,integral_const_mul,
    integral_comp_mul_left_Ioi (fun t => t^k*F t) 0 hκ]
  simp only [mul_zero,smul_eq_mul,pow_succ,div_eq_mul_inv,mul_inv_rev]
  ring

lemma etaStar_moment_integrable (k : ℕ) :
    IntegrableOn (fun t : ℝ => t^k*etaStar t) (Ioi (0 : ℝ)) := by
  have hmc := (mellin_etaTwo_phi_moment k).1
  have hs : IntegrableOn (fun t : ℝ => (49*t)^k*mellinConv etaTwo phi (49*t)) (Ioi (0 : ℝ)) := by
    apply (integrableOn_Ioi_comp_mul_left_iff
      (fun t => t^k*mellinConv etaTwo phi t) 0 (by norm_num : (0 : ℝ) < 49)).mpr
    simpa using hmc
  have hh := hs.const_mul ((49 : ℝ)^k)⁻¹
  have heq : (fun t : ℝ => t^k*etaStar t) =
      fun t => ((49 : ℝ)^k)⁻¹*((49*t)^k*mellinConv etaTwo phi (49*t)) := by
    funext t
    unfold etaStar
    rw [mul_pow]
    field_simp
  rw [heq]
  exact hh

lemma etaStar_moment_formula (k : ℕ) :
    (∫ t in Ioi (0 : ℝ), t^k*etaStar t) =
      ((∫ t : ℝ, t^k*etaTwo t)*(∫ t in Ioi (0 : ℝ), t^k*phi t))/(49 : ℝ)^(k+1) := by
  unfold etaStar
  rw [scaled_moment_integral _ 49 (by norm_num), (mellin_etaTwo_phi_moment k).2]

theorem etaStar_moments :
    (∫ t in Ioi (0 : ℝ), etaStar t) = Real.sqrt (Real.pi/2)/49 ∧
    (∫ t in Ioi (0 : ℝ), t*etaStar t) = (9/19208 : ℝ) ∧
    (∫ t in Ioi (0 : ℝ), t^2*etaStar t) = Real.sqrt (Real.pi/2)/115248 := by
  constructor
  · have h := etaStar_moment_formula 0
    simpa [etaTwo_mass,phi_mass] using h
  constructor
  · have h := etaStar_moment_formula 1
    norm_num [etaTwo_first_moment,phi_first_moment] at h
    simpa using h
  · rw [etaStar_moment_formula 2,etaTwo_second_moment,phi_second_moment]
    norm_num
    ring

end Helfgott
end

section
open MeasureTheory Set Filter
open scoped Convolution

namespace Helfgott

lemma etaCircle_le_one (t : ℝ) : etaCircle t ≤ 1 := by
  by_cases ht : t ∈ Icc (0 : ℝ) 2
  · have htn : 0 ≤ t*(2-t) := mul_nonneg ht.1 (by linarith [ht.2])
    have htl : t*(2-t) ≤ 1 := by nlinarith [sq_nonneg (t-1)]
    have hp : (t*(2-t))^3 ≤ 1 := by
      simpa using pow_le_pow_left₀ htn htl 3
    have he : Real.exp (-((t-1)^2)/2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (t-1)])
    rw [etaCircle,indicator_of_mem ht]
    have heq : t^3*(2-t)^3 = (t*(2-t))^3 := by ring
    rw [heq]
    exact mul_le_one₀ hp (by positivity) he
  · simp [etaCircle,ht]

lemma etaCircle_convolution_continuous :
    Continuous (fun ρ : ℝ => ∫ u : ℝ, etaCircle u*etaCircle (ρ-u)) := by
  have h := etaCircle_hasCompactSupport.continuous_convolution_right
    (L := ContinuousLinearMap.lsmul ℝ ℝ) etaCircle_integrable.locallyIntegrable etaCircle_continuous
  exact h

lemma etaCircle_convolution_nonneg (ρ : ℝ) :
    0 ≤ ∫ u : ℝ, etaCircle u*etaCircle (ρ-u) := by
  apply integral_nonneg
  intro u
  exact mul_nonneg (etaCircle_nonneg u) (etaCircle_nonneg (ρ-u))

lemma etaCircle_convolution_le (ρ : ℝ) :
    (∫ u : ℝ, etaCircle u*etaCircle (ρ-u)) ≤ ∫ u : ℝ, etaCircle u := by
  have hc : Continuous (fun u : ℝ => etaCircle u*etaCircle (ρ-u)) :=
    etaCircle_continuous.mul (etaCircle_continuous.comp (continuous_const.sub continuous_id))
  have hi : Integrable (fun u : ℝ => etaCircle u*etaCircle (ρ-u)) :=
    hc.integrable_of_hasCompactSupport etaCircle_hasCompactSupport.mul_right
  apply integral_mono hi etaCircle_integrable
  intro u
  exact mul_le_of_le_one_right (etaCircle_nonneg u) (etaCircle_le_one (ρ-u))

lemma main_convolution_integrable (ρ : ℝ) :
    IntegrableOn (fun w : ℝ => etaStar w*(∫ u : ℝ, etaCircle u*etaCircle (ρ-w-u)))
      (Ioi (0 : ℝ)) := by
  have hs : IntegrableOn etaStar (Ioi (0 : ℝ)) := by
    simpa using etaStar_moment_integrable 0
  have hc : Continuous (fun w : ℝ => ∫ u : ℝ, etaCircle u*etaCircle (ρ-w-u)) :=
    etaCircle_convolution_continuous.comp (continuous_const.sub continuous_id)
  apply (hs.mul_const (∫ u : ℝ, etaCircle u)).mono'
  · exact hs.aestronglyMeasurable.mul hc.aestronglyMeasurable
  · exact Eventually.of_forall (fun w => by
      have hn : 0 ≤ etaStar w := mellin_etaTwo_phi_nonneg (49*w)
      have hcn := etaCircle_convolution_nonneg (ρ-w)
      rw [Real.norm_of_nonneg (mul_nonneg hn hcn)]
      exact mul_le_mul_of_nonneg_left (etaCircle_convolution_le (ρ-w)) hn)

lemma main_convolution_lower (ρ : ℝ) :
    (16/25 : ℝ)*(∫ w in Ioi (0 : ℝ), etaStar w) -
      (17/10 : ℝ)*(∫ w in Ioi (0 : ℝ), etaStar w*((ρ-2)-w)^2) ≤
    ∫ w in Ioi (0 : ℝ), etaStar w*(∫ u : ℝ, etaCircle u*etaCircle (ρ-w-u)) := by
  have hs : IntegrableOn etaStar (Ioi (0 : ℝ)) := by simpa using etaStar_moment_integrable 0
  have h1 : IntegrableOn (fun w : ℝ => w*etaStar w) (Ioi (0 : ℝ)) := by
    simpa using etaStar_moment_integrable 1
  have h2 := etaStar_moment_integrable 2
  have hi : IntegrableOn (fun w : ℝ => etaStar w*((ρ-2)-w)^2) (Ioi (0 : ℝ)) := by
    have h := ((hs.const_mul ((ρ-2)^2)).sub (h1.const_mul (2*(ρ-2)))).add h2
    have heq : (fun w : ℝ => etaStar w*((ρ-2)-w)^2) =
        (((fun w => (ρ-2)^2*etaStar w) - fun w => 2*(ρ-2)*(w*etaStar w)) +
          fun w => w^2*etaStar w) := by
      funext w
      dsimp only [Pi.add_apply,Pi.sub_apply]
      ring
    rw [heq]
    exact h
  have hh : (∫ w in Ioi (0 : ℝ), (16/25 : ℝ)*etaStar w -
      (17/10 : ℝ)*(etaStar w*((ρ-2)-w)^2)) ≤
      ∫ w in Ioi (0 : ℝ), etaStar w*(∫ u : ℝ, etaCircle u*etaCircle (ρ-w-u)) := by
    apply integral_mono ((hs.const_mul (16/25)).sub (hi.const_mul (17/10)))
      (main_convolution_integrable ρ)
    intro w
    have hn : 0 ≤ etaStar w := mellin_etaTwo_phi_nonneg (49*w)
    have h := mul_le_mul_of_nonneg_left (etaCircle_convolution_lower (ρ-w)) hn
    convert! h using 1 <;> dsimp only [Pi.sub_apply] <;> ring
  rw [integral_sub (hs.const_mul (16/25)) (hi.const_mul (17/10)),
    integral_const_mul,integral_const_mul] at hh
  exact hh

lemma etaStar_centered_square_integral (a : ℝ) :
    (∫ w in Ioi (0 : ℝ), etaStar w*(a-w)^2) =
      a^2*(Real.sqrt (Real.pi/2)/49) - 2*a*(9/19208 : ℝ) +
        Real.sqrt (Real.pi/2)/115248 := by
  have hs : IntegrableOn etaStar (Ioi (0 : ℝ)) := by simpa using etaStar_moment_integrable 0
  have h1 : IntegrableOn (fun w : ℝ => w*etaStar w) (Ioi (0 : ℝ)) := by
    simpa using etaStar_moment_integrable 1
  have h2 := etaStar_moment_integrable 2
  have heq : (fun w : ℝ => etaStar w*(a-w)^2) =
      fun w => a^2*etaStar w - (2*a)*(w*etaStar w) + w^2*etaStar w := by
    funext w; ring
  rw [heq,integral_add (f := fun w : ℝ => a^2*etaStar w - (2*a)*(w*etaStar w))
      (g := fun w : ℝ => w^2*etaStar w) ((hs.const_mul (a^2)).sub (h1.const_mul (2*a))) h2,
    integral_sub (f := fun w : ℝ => a^2*etaStar w) (g := fun w : ℝ => (2*a)*(w*etaStar w))
      (hs.const_mul (a^2)) (h1.const_mul (2*a)),integral_const_mul,integral_const_mul,
    etaStar_moments.1,etaStar_moments.2.1,etaStar_moments.2.2]

lemma main_convolution_lower_centered :
    (801/49000 : ℝ) ≤
      ∫ w in Ioi (0 : ℝ), etaStar w*(∫ u : ℝ,
        etaCircle u*etaCircle (2+9/(392*Real.sqrt (Real.pi/2))-w-u)) := by
  let A : ℝ := Real.sqrt (Real.pi/2)
  let a : ℝ := 9/(392*A)
  have hA : 0 < A := Real.sqrt_pos.mpr (by positivity)
  have hAl : (1253/1000 : ℝ) ≤ A := by
    have hs : A^2 = Real.pi/2 := Real.sq_sqrt (by positivity)
    have hn : 0 ≤ A := hA.le
    nlinarith [Real.pi_gt_d4]
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hrel : a*A/49 = (9/19208 : ℝ) := by
    dsimp [a]
    field_simp
    all_goals ring
  have hv : (∫ w in Ioi (0 : ℝ), etaStar w*(a-w)^2) ≤ A/115248 := by
    rw [etaStar_centered_square_integral]
    change a^2*(A/49)-2*a*(9/19208 : ℝ)+A/115248 ≤ A/115248
    have hmul := mul_nonneg ha (by norm_num : (0 : ℝ) ≤ 9/19208)
    have hh : a^2*(A/49) = a*(9/19208 : ℝ) := by rw [← hrel]; ring
    rw [hh]
    nlinarith
  have hb := main_convolution_lower (2+a)
  have heq : ((2+a)-2) = a := by ring
  rw [heq,etaStar_moments.1] at hb
  have hh := mul_le_mul_of_nonneg_left hv (by norm_num : (0 : ℝ) ≤ 17/10)
  have hnum : (801/49000 : ℝ) ≤ (16/25 : ℝ)*(A/49)-(17/10 : ℝ)*(A/115248) := by
    nlinarith only [hAl]
  exact hnum.trans ((sub_le_sub_left hh _).trans hb)

lemma goldbach_center_eq :
    9/(196*Real.sqrt (2*Real.pi)) = 9/(392*Real.sqrt (Real.pi/2)) := by
  have hs : Real.sqrt (2*Real.pi) = 2*Real.sqrt (Real.pi/2) := by
    have h1 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2*Real.pi)
    have h2 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ Real.pi/2)
    have h3 := Real.sqrt_nonneg (2*Real.pi)
    have h4 := Real.sqrt_nonneg (Real.pi/2)
    nlinarith
  rw [hs]
  congr 1
  ring

theorem etaCircle_etaStar_main_convolution_lower :
    (801/49000 : ℝ) ≤
      ∫ w in Ioi (0 : ℝ), etaStar w*(∫ u : ℝ,
        etaCircle u*etaCircle (2+9/(196*Real.sqrt (2*Real.pi))-w-u)) := by
  rw [goldbach_center_eq]
  exact main_convolution_lower_centered

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open MeasureTheory Set
open scoped Interval
namespace Helfgott
lemma exp_neg_upper_quartic (u : ℝ) (hu : 0≤u) :
    Real.exp (-u)≤1-u+u^2/2-u^3/6+u^4/24 := by
  let g : ℝ → ℝ := fun t => 1-t+t^2/2-t^3/6+t^4/24-Real.exp (-t)
  have hd (t : ℝ) : HasDerivAt g (Real.exp (-t)-(1-t+t^2/2-t^3/6)) t := by
    dsimp [g]
    convert! ((((((hasDerivAt_const t (0 : ℝ)).add (hasDerivAt_const t (1 : ℝ))).add (((hasDerivAt_id t).pow 1).const_mul (-1/1 : ℝ))).add (((hasDerivAt_id t).pow 2).const_mul (1/2 : ℝ))).add (((hasDerivAt_id t).pow 3).const_mul (-1/6 : ℝ))).add (((hasDerivAt_id t).pow 4).const_mul (1/24 : ℝ))).sub (((hasDerivAt_id t).neg).exp) using 1
    all_goals try funext x
    all_goals simp
    all_goals ring
  have hm : MonotoneOn g (Ici 0) := monotoneOn_of_hasDerivWithinAt_nonneg
    (convex_Ici 0) (by dsimp [g]; fun_prop)
    (fun t _ => (hd t).hasDerivWithinAt) (fun t ht =>
      sub_nonneg.mpr (exp_neg_lower_cubic t (mem_Ici.mp (interior_subset ht))))
  have h := hm (by simp : (0 : ℝ)∈Ici 0) hu hu
  dsimp [g] at h
  norm_num at h
  linarith
lemma exp_neg_lower_quintic (u : ℝ) (hu : 0≤u) :
    1-u+u^2/2-u^3/6+u^4/24-u^5/120≤Real.exp (-u) := by
  let g : ℝ → ℝ := fun t => Real.exp (-t)-1+t-t^2/2+t^3/6-t^4/24+t^5/120
  have hd (t : ℝ) : HasDerivAt g (1-t+t^2/2-t^3/6+t^4/24-Real.exp (-t)) t := by
    dsimp [g]
    convert! (((hasDerivAt_id t).neg).exp).sub (((((((hasDerivAt_const t (0 : ℝ)).add (hasDerivAt_const t (1 : ℝ))).add (((hasDerivAt_id t).pow 1).const_mul (-1/1 : ℝ))).add (((hasDerivAt_id t).pow 2).const_mul (1/2 : ℝ))).add (((hasDerivAt_id t).pow 3).const_mul (-1/6 : ℝ))).add (((hasDerivAt_id t).pow 4).const_mul (1/24 : ℝ))).add (((hasDerivAt_id t).pow 5).const_mul (-1/120 : ℝ))) using 1
    all_goals try funext x
    all_goals simp
    all_goals ring
  have hm : MonotoneOn g (Ici 0) := monotoneOn_of_hasDerivWithinAt_nonneg
    (convex_Ici 0) (by dsimp [g]; fun_prop)
    (fun t _ => (hd t).hasDerivWithinAt) (fun t ht =>
      sub_nonneg.mpr (exp_neg_upper_quartic t (mem_Ici.mp (interior_subset ht))))
  have h := hm (by simp : (0 : ℝ)∈Ici 0) hu hu
  dsimp [g] at h
  norm_num at h
  linarith

theorem symmetric_smoothing_l2_lower_tight :
    (3201/5000 : ℝ)≤∫ t in (-1 : ℝ)..1,((1-t^2)^3*Real.exp (-(t^2)/2))^2 := by
  let P : ℝ → ℝ := fun t => (1-t^2)^6*(1-t^2+t^4/2-t^6/6+t^8/24-t^10/120)
  have hpoint (t : ℝ) : P t≤((1-t^2)^3*Real.exp (-(t^2)/2))^2 := by
    have he := exp_neg_lower_quintic (t^2) (sq_nonneg t)
    have hexp : Real.exp (-(t^2)/2)^2=Real.exp (-(t^2)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hm := mul_le_mul_of_nonneg_left he (show 0≤(1-t^2)^6 by positivity)
    convert! hm using 1 <;> simp only [P,mul_pow,pow_mul,neg_sq,hexp] <;> ring
  let Q : ℝ → ℝ := fun t => (1/1 : ℝ)*t^1 + (-7/3 : ℝ)*t^3 + (43/10 : ℝ)*t^5 + (-229/42 : ℝ)*t^7 + (1045/216 : ℝ)*t^9 + (-4051/1320 : ℝ)*t^11 + (2221/1560 : ℝ)*t^13 + (-179/360 : ℝ)*t^15 + (55/408 : ℝ)*t^17 + (-13/456 : ℝ)*t^19 + (11/2520 : ℝ)*t^21 + (-1/2760 : ℝ)*t^23
  have hQ (t : ℝ) : HasDerivAt Q (P t) t := by
    dsimp [Q,P]
    convert! ((((((((((((hasDerivAt_const t (0 : ℝ)).add ((((hasDerivAt_id t).pow 1).const_mul (1/1 : ℝ)).div_const 1)).add ((((hasDerivAt_id t).pow 3).const_mul (-7/1 : ℝ)).div_const 3)).add ((((hasDerivAt_id t).pow 5).const_mul (43/2 : ℝ)).div_const 5)).add ((((hasDerivAt_id t).pow 7).const_mul (-229/6 : ℝ)).div_const 7)).add ((((hasDerivAt_id t).pow 9).const_mul (1045/24 : ℝ)).div_const 9)).add ((((hasDerivAt_id t).pow 11).const_mul (-4051/120 : ℝ)).div_const 11)).add ((((hasDerivAt_id t).pow 13).const_mul (2221/120 : ℝ)).div_const 13)).add ((((hasDerivAt_id t).pow 15).const_mul (-179/24 : ℝ)).div_const 15)).add ((((hasDerivAt_id t).pow 17).const_mul (55/24 : ℝ)).div_const 17)).add ((((hasDerivAt_id t).pow 19).const_mul (-13/24 : ℝ)).div_const 19)).add ((((hasDerivAt_id t).pow 21).const_mul (11/120 : ℝ)).div_const 21)).add ((((hasDerivAt_id t).pow 23).const_mul (-1/120 : ℝ)).div_const 23) using 1
    all_goals try funext x
    all_goals simp
    all_goals ring
  have hpint : (∫ t in (-1 : ℝ)..1,P t)=(642714112/1003917915 : ℝ) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hQ t)
      ((by dsimp [P]; fun_prop : Continuous P).intervalIntegrable _ _)]
    norm_num [Q]
  have hm : (∫ t in (-1 : ℝ)..1,P t)≤∫ t in (-1 : ℝ)..1,((1-t^2)^3*Real.exp (-(t^2)/2))^2 := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact (by dsimp [P]; fun_prop : Continuous P).intervalIntegrable _ _
    · exact (by fun_prop : Continuous (fun t : ℝ => ((1-t^2)^3*Real.exp (-(t^2)/2))^2)).intervalIntegrable _ _
    · intro t _; exact hpoint t
  rw [hpint] at hm
  exact (by norm_num : (3201/5000 : ℝ)≤(642714112/1003917915 : ℝ)).trans hm

theorem symmetric_smoothing_derivative_l2_upper_tight :
    (∫ t in (-1 : ℝ)..1,(-t*(1-t^2)^2*(7-t^2)*Real.exp (-(t^2)/2))^2)≤(137/50 : ℝ) := by
  let P : ℝ → ℝ := fun t => t^2*(1-t^2)^4*(7-t^2)^2*(1-t^2+t^4/2-t^6/6+t^8/24)
  have hpoint (t : ℝ) : (-t*(1-t^2)^2*(7-t^2)*Real.exp (-(t^2)/2))^2≤P t := by
    have he := exp_neg_upper_quartic (t^2) (sq_nonneg t)
    have hexp : Real.exp (-(t^2)/2)^2=Real.exp (-(t^2)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hm := mul_le_mul_of_nonneg_left he (show 0≤t^2*(1-t^2)^4*(7-t^2)^2 by positivity)
    convert! hm using 1 <;> simp only [P,mul_pow,pow_mul,neg_sq,hexp] <;> ring
  let Q : ℝ → ℝ := fun t => (49/3 : ℝ)*t^3 + (-259/5 : ℝ)*t^5 + (1171/14 : ℝ)*t^7 + (-4489/54 : ℝ)*t^9 + (14581/264 : ℝ)*t^11 + (-1353/52 : ℝ)*t^13 + (655/72 : ℝ)*t^15 + (-121/51 : ℝ)*t^17 + (65/152 : ℝ)*t^19 + (-11/252 : ℝ)*t^21 + (1/552 : ℝ)*t^23
  have hQ (t : ℝ) : HasDerivAt Q (P t) t := by
    dsimp [Q,P]
    convert! (((((((((((hasDerivAt_const t (0 : ℝ)).add ((((hasDerivAt_id t).pow 3).const_mul (49/1 : ℝ)).div_const 3)).add ((((hasDerivAt_id t).pow 5).const_mul (-259/1 : ℝ)).div_const 5)).add ((((hasDerivAt_id t).pow 7).const_mul (1171/2 : ℝ)).div_const 7)).add ((((hasDerivAt_id t).pow 9).const_mul (-4489/6 : ℝ)).div_const 9)).add ((((hasDerivAt_id t).pow 11).const_mul (14581/24 : ℝ)).div_const 11)).add ((((hasDerivAt_id t).pow 13).const_mul (-1353/4 : ℝ)).div_const 13)).add ((((hasDerivAt_id t).pow 15).const_mul (3275/24 : ℝ)).div_const 15)).add ((((hasDerivAt_id t).pow 17).const_mul (-121/3 : ℝ)).div_const 17)).add ((((hasDerivAt_id t).pow 19).const_mul (65/8 : ℝ)).div_const 19)).add ((((hasDerivAt_id t).pow 21).const_mul (-11/12 : ℝ)).div_const 21)).add ((((hasDerivAt_id t).pow 23).const_mul (1/24 : ℝ)).div_const 23) using 1
    all_goals try funext x
    all_goals simp
    all_goals ring
  have hpint : (∫ t in (-1 : ℝ)..1,P t)=(2748438656/1003917915 : ℝ) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hQ t)
      ((by dsimp [P]; fun_prop : Continuous P).intervalIntegrable _ _)]
    norm_num [Q]
  have hm : (∫ t in (-1 : ℝ)..1,(-t*(1-t^2)^2*(7-t^2)*Real.exp (-(t^2)/2))^2)≤∫ t in (-1 : ℝ)..1,P t := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact (by fun_prop : Continuous (fun t : ℝ => (-t*(1-t^2)^2*(7-t^2)*Real.exp (-(t^2)/2))^2)).intervalIntegrable _ _
    · exact (by dsimp [P]; fun_prop : Continuous P).intervalIntegrable _ _
    · intro t _; exact hpoint t
  rw [hpint] at hm
  exact hm.trans (by norm_num)

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Interval
namespace Helfgott
noncomputable def referenceFirstDerivative (t : ℝ) : ℝ :=
  ((Icc (0 : ℝ) 2).indicator (fun t =>
    -(t-1)*(1-(t-1)^2)^2*(7-(t-1)^2)*Real.exp (-((t-1)^2)/2)) t)
lemma etaCircle_mass_lower_tight : (3201/5000 : ℝ) ≤ ∫ t : ℝ, (etaCircle t)^2 := by
  have heq : (∫ t : ℝ, (etaCircle t)^2) =
      ∫ t in (-1 : ℝ)..1, ((1-t^2)^3 * Real.exp (-(t^2)/2))^2 := by
    calc
      (∫ t : ℝ, (etaCircle t)^2) =
          ∫ t : ℝ, (Set.Icc (0 : ℝ) 2).indicator
            (fun t => (t^3*(2-t)^3*Real.exp (-((t-1)^2)/2))^2) t := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun t => by
          by_cases ht : t ∈ Set.Icc (0 : ℝ) 2 <;> simp [etaCircle,ht])
      _ = ∫ t in (0 : ℝ)..2, (t^3*(2-t)^3*Real.exp (-((t-1)^2)/2))^2 := by
        rw [integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
          intervalIntegral.integral_of_le (by norm_num)]
      _ = ∫ t in (-1 : ℝ)..1,
          ((t+1)^3*(2-(t+1))^3*Real.exp (-(((t+1)-1)^2)/2))^2 := by
        simpa only [neg_add_cancel,one_add_one_eq_two] using
          (intervalIntegral.integral_comp_add_right
            (fun t : ℝ => (t^3*(2-t)^3*Real.exp (-((t-1)^2)/2))^2) 1
            (a := (-1 : ℝ)) (b := 1)).symm
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro t _
        simp only [add_sub_cancel_right]
        ring
  rw [heq]
  exact symmetric_smoothing_l2_lower_tight

lemma referenceFirstDerivative_energy_upper_tight : (∫ t : ℝ, (referenceFirstDerivative t)^2) ≤ (137/50 : ℝ) := by
  have heq : (∫ t : ℝ, (referenceFirstDerivative t)^2) =
      ∫ t in (-1 : ℝ)..1,
        (-t*(1-t^2)^2*(7-t^2)*Real.exp (-(t^2)/2))^2 := by
    calc
      (∫ t : ℝ, (referenceFirstDerivative t)^2) =
          ∫ t : ℝ, (Set.Icc (0 : ℝ) 2).indicator
            (fun t => (-(t-1)*(1-(t-1)^2)^2*(7-(t-1)^2)*Real.exp (-((t-1)^2)/2))^2) t := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun t => by
          by_cases ht : t ∈ Set.Icc (0 : ℝ) 2 <;> simp [referenceFirstDerivative,ht])
      _ = ∫ t in (0 : ℝ)..2,
          (-(t-1)*(1-(t-1)^2)^2*(7-(t-1)^2)*Real.exp (-((t-1)^2)/2))^2 := by
        rw [integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
          intervalIntegral.integral_of_le (by norm_num)]
      _ = _ := by
        simpa only [neg_add_cancel,one_add_one_eq_two,add_sub_cancel_right] using
          (intervalIntegral.integral_comp_add_right
            (fun t : ℝ => (-(t-1)*(1-(t-1)^2)^2*(7-(t-1)^2)*Real.exp (-((t-1)^2)/2))^2) 1
            (a := (-1 : ℝ)) (b := 1)).symm
  rw [heq]
  exact symmetric_smoothing_derivative_l2_upper_tight

theorem etaCircle_convolution_lower_tight (ρ : ℝ) :
    (3201/5000 : ℝ) - (137/100 : ℝ)*(ρ-2)^2 ≤
      ∫ t : ℝ, etaCircle t * etaCircle (ρ-t) := by
  have hg : Continuous referenceFirstDerivative := etaCircle_deriv_continuous
  have hg2 : Integrable (fun t => (referenceFirstDerivative t)^2) := etaCircle_deriv_square_integrable
  have hder (t : ℝ) : HasDerivAt etaCircle (referenceFirstDerivative t) t := etaCircle_hasDerivAt t
  have hb := translated_product_lower etaCircle referenceFirstDerivative etaCircle_continuous
    etaCircle_hasCompactSupport hg hg2 hder (2-ρ)
  have heq : (∫ t : ℝ, etaCircle t * etaCircle (t+(2-ρ))) =
      ∫ t : ℝ, etaCircle t * etaCircle (ρ-t) := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun t => by
      change etaCircle t * etaCircle (t+(2-ρ)) = etaCircle t * etaCircle (ρ-t)
      rw [← etaCircle_symmetric (ρ-t)]
      congr 2
      ring)
  rw [heq] at hb
  have henergy := referenceFirstDerivative_energy_upper_tight
  have hmass := etaCircle_mass_lower_tight
  have hcoef : 0 ≤ (2-ρ)^2/2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left henergy hcoef
  have hs : (2-ρ)^2 = (ρ-2)^2 := by ring
  rw [hs] at hb hmul
  linarith

lemma main_convolution_lower_tight (ρ : ℝ) :
    (3201/5000 : ℝ)*(∫ w in Ioi (0 : ℝ), etaStar w) -
      (137/100 : ℝ)*(∫ w in Ioi (0 : ℝ), etaStar w*((ρ-2)-w)^2) ≤
    ∫ w in Ioi (0 : ℝ), etaStar w*(∫ u : ℝ, etaCircle u*etaCircle (ρ-w-u)) := by
  have hs : IntegrableOn etaStar (Ioi (0 : ℝ)) := by simpa using etaStar_moment_integrable 0
  have h1 : IntegrableOn (fun w : ℝ => w*etaStar w) (Ioi (0 : ℝ)) := by
    simpa using etaStar_moment_integrable 1
  have h2 := etaStar_moment_integrable 2
  have hi : IntegrableOn (fun w : ℝ => etaStar w*((ρ-2)-w)^2) (Ioi (0 : ℝ)) := by
    have h := ((hs.const_mul ((ρ-2)^2)).sub (h1.const_mul (2*(ρ-2)))).add h2
    have heq : (fun w : ℝ => etaStar w*((ρ-2)-w)^2) =
        (((fun w => (ρ-2)^2*etaStar w) - fun w => 2*(ρ-2)*(w*etaStar w)) +
          fun w => w^2*etaStar w) := by
      funext w
      dsimp only [Pi.add_apply,Pi.sub_apply]
      ring
    rw [heq]
    exact h
  have hh : (∫ w in Ioi (0 : ℝ), (3201/5000 : ℝ)*etaStar w -
      (137/100 : ℝ)*(etaStar w*((ρ-2)-w)^2)) ≤
      ∫ w in Ioi (0 : ℝ), etaStar w*(∫ u : ℝ, etaCircle u*etaCircle (ρ-w-u)) := by
    apply integral_mono ((hs.const_mul (3201/5000)).sub (hi.const_mul (137/100)))
      (main_convolution_integrable ρ)
    intro w
    have hn : 0 ≤ etaStar w := mellin_etaTwo_phi_nonneg (49*w)
    have h := mul_le_mul_of_nonneg_left (etaCircle_convolution_lower_tight (ρ-w)) hn
    convert! h using 1 <;> dsimp only [Pi.sub_apply] <;> ring
  rw [integral_sub (hs.const_mul (3201/5000)) (hi.const_mul (137/100)),
    integral_const_mul,integral_const_mul] at hh
  exact hh


lemma etaStar_centered_square_integral_tight :
    (∫ w in Ioi (0 : ℝ),etaStar w*(9/(392*Real.sqrt (Real.pi/2))-w)^2)≤
      (9/80000 : ℝ)/49 := by
  let A : ℝ := Real.sqrt (Real.pi/2)
  let a : ℝ := 9/(392*A)
  have hA : 0<A := Real.sqrt_pos.mpr (by positivity)
  have hAl : (1253314/1000000 : ℝ)≤A := by
    have hs : A^2=Real.pi/2 := Real.sq_sqrt (by positivity)
    nlinarith [Real.pi_gt_d6]
  have hAu : A≤(1253315/1000000 : ℝ) := by
    have hs : A^2=Real.pi/2 := Real.sq_sqrt (by positivity)
    nlinarith [Real.pi_lt_d6]
  have hrel : a*A/49=(9/19208 : ℝ) := by
    dsimp [a]
    field_simp
    norm_num
  have hprod : a*A=9/392 := by nlinarith [hrel]
  have hapos : 0≤a := by dsimp [a]; positivity
  have hal : (18318/1000000 : ℝ)≤a := by nlinarith [hprod]
  have ha2 : a^2*(A/49)=a*(9/19208 : ℝ) := by rw [←hrel]; ring
  rw [etaStar_centered_square_integral]
  change a^2*(A/49)-2*a*(9/19208 : ℝ)+A/115248≤_
  rw [ha2]
  nlinarith

theorem etaCircle_etaStar_main_convolution_lower_tight :
    (4011/5000 : ℝ)/49≤
      ∫ w in Ioi (0 : ℝ),etaStar w*(∫ u : ℝ,
        etaCircle u*etaCircle (2+9/(196*Real.sqrt (2*Real.pi))-w-u)) := by
  rw [goldbach_center_eq]
  have hb := main_convolution_lower_tight (2+9/(392*Real.sqrt (Real.pi/2)))
  simp only [add_sub_cancel_left] at hb
  rw [etaStar_moments.1] at hb
  have hAl : (1253314/1000000 : ℝ)≤Real.sqrt (Real.pi/2) := by
    have hs := Real.sq_sqrt (by positivity : (0 : ℝ)≤Real.pi/2)
    nlinarith [Real.sqrt_nonneg (Real.pi/2),Real.pi_gt_d6]
  have hv := etaStar_centered_square_integral_tight
  nlinarith
end Helfgott
end

open MeasureTheory Helfgott
theorem solution :
    (4011/5000 : ℝ)/49≤
      ∫ w in Set.Ioi (0 : ℝ),etaStar w*(∫ u : ℝ,
        etaCircle u*etaCircle (2+9/(196*Real.sqrt (2*Real.pi))-w-u)) := etaCircle_etaStar_main_convolution_lower_tight
#print axioms solution
