-- Prove2me | solution 1 for Helfgott.etaCircle_convolution_lower
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T21:38:46.666672+00:00
-- url     : https://prove2.me/submissions/582b36d4-ea8f-4e0b-ae11-718165e4f644

import Definitions.Def_Helfgott_Smoothings
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Full proof of the symmetric smoothing convolution lower bound.
All regularity, integration, translation and polynomial helper proofs are included.
No unproved platform theorem or local Solutions module is imported.
Written by Codex. -/


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


theorem solution (ρ : ℝ) :
    (16/25 : ℝ) - (17/10 : ℝ)*(ρ-2)^2 ≤
      ∫ t : ℝ, Helfgott.etaCircle t * Helfgott.etaCircle (ρ-t) :=
  Helfgott.etaCircle_convolution_lower ρ

#print axioms solution
