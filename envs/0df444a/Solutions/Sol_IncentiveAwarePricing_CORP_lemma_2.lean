-- Prove2me | solution 1 for IncentiveAwarePricing.CORP.lemma_2
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-10-22T04:22:25.148674+00:00
-- url     : https://prove2.me/submissions/9f1cc7a0-2fd8-45b2-99ea-3d9fb1346284

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_IncentiveAwarePricing_CORP_Model

open MeasureTheory
open scoped RealInnerProductSpace ENNReal
open IncentiveAwarePricing.CORP

namespace CorpL2Counter

/-- clamp of the affine map `(z + 8) / 15` to `[0, 1]`. -/
noncomputable def cl (z : ℝ) : ℝ := max 0 (min 1 ((z + 8) / 15))

/-- The counterexample density on `[-8, 7]`. -/
noncomputable def fE (z : ℝ) : ℝ := 4 / 15 * (cl z * (1 - cl z ^ 2))

def Φ (u : ℝ) : ℝ := u ^ 2 * (2 - u ^ 2)

def Ψ (u : ℝ) : ℝ := (1 - u ^ 2) ^ 2

lemma cl_nonneg (z : ℝ) : 0 ≤ cl z := le_max_left _ _
lemma cl_le_one (z : ℝ) : cl z ≤ 1 := max_le zero_le_one (min_le_left _ _)

lemma cl_of_le {z : ℝ} (h : z ≤ -8) : cl z = 0 := by
  unfold cl; apply max_eq_left; apply min_le_of_right_le; linarith

lemma cl_of_ge {z : ℝ} (h : 7 ≤ z) : cl z = 1 := by
  unfold cl; rw [min_eq_left (by linarith)]; simp

lemma cl_of_mem {z : ℝ} (h1 : -8 ≤ z) (h2 : z ≤ 7) : cl z = (z + 8) / 15 := by
  unfold cl; rw [min_eq_right (by linarith), max_eq_right (by linarith)]

lemma continuous_cl : Continuous cl := by
  unfold cl; fun_prop

lemma continuous_fE : Continuous fE := by
  unfold fE; have := continuous_cl; fun_prop

lemma fE_eq_zero_of_le {z : ℝ} (h : z ≤ -8) : fE z = 0 := by
  simp [fE, cl_of_le h]

lemma fE_eq_zero_of_ge {z : ℝ} (h : 7 ≤ z) : fE z = 0 := by
  simp [fE, cl_of_ge h]

lemma fE_nonneg (z : ℝ) : 0 ≤ fE z := by
  unfold fE
  have h0 := cl_nonneg z; have h1 := cl_le_one z
  apply mul_nonneg (by norm_num); apply mul_nonneg h0; nlinarith

lemma hasCompactSupport_fE : HasCompactSupport fE := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (-8 : ℝ)) (b := 7))
  intro z hz
  simp only [Set.mem_Icc, not_and_or, not_le] at hz
  rcases hz with h | h
  · exact fE_eq_zero_of_le h.le
  · exact fE_eq_zero_of_ge h.le

lemma integrable_fE : Integrable fE := continuous_fE.integrable_of_hasCompactSupport hasCompactSupport_fE

/-- polynomial form on `[-8, 7]` -/
noncomputable def pE (t : ℝ) : ℝ := 4 / 15 * ((t + 8) / 15 * (1 - ((t + 8) / 15) ^ 2))

lemma hasDerivAt_P (t : ℝ) : HasDerivAt (fun t => Φ ((t + 8) / 15)) (pE t) t := by
  have hu : HasDerivAt (fun t : ℝ => (t + 8) / 15) (1 / 15) t := by
    simpa using ((hasDerivAt_id t).add_const 8).div_const 15
  have := (hu.pow 2).mul ((hu.pow 2).const_sub 2)
  unfold Φ
  refine this.congr_deriv ?_
  simp only [Pi.pow_apply, pE]
  norm_num
  ring

lemma hasDerivAt_Q (t : ℝ) :
    HasDerivAt (fun t => 4 * (5 * ((t + 8) / 15) ^ 3 - 3 * ((t + 8) / 15) ^ 5
      - 4 * ((t + 8) / 15) ^ 2 + 2 * ((t + 8) / 15) ^ 4)) (t * pE t) t := by
  have hu : HasDerivAt (fun t : ℝ => (t + 8) / 15) (1 / 15) t := by
    simpa using ((hasDerivAt_id t).add_const 8).div_const 15
  have := ((((hu.pow 3).const_mul 5).sub ((hu.pow 5).const_mul 3)).sub
    ((hu.pow 2).const_mul 4)).add ((hu.pow 4).const_mul 2) |>.const_mul 4
  refine this.congr_deriv ?_
  simp only [Pi.pow_apply, pE]
  norm_num
  ring

lemma intervalIntegral_fE {w : ℝ} (h1 : -8 ≤ w) (h2 : w ≤ 7) :
    ∫ t in (-8 : ℝ)..w, fE t = Φ ((w + 8) / 15) := by
  have hcongr : Set.EqOn fE pE (Set.uIcc (-8) w) := by
    intro t ht
    rw [Set.uIcc_of_le h1] at ht
    simp only [fE, pE, cl_of_mem ht.1 (ht.2.trans h2)]
  rw [intervalIntegral.integral_congr hcongr,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_P t)
      ((by unfold pE; fun_prop : Continuous pE).intervalIntegrable _ _)]
  simp [Φ]

lemma intervalIntegral_zero_part {a b : ℝ} (ha : 7 ≤ a) (hab : a ≤ b) (g : ℝ → ℝ) :
    ∫ t in a..b, g t * fE t = 0 := by
  have : Set.EqOn (fun t => g t * fE t) (fun _ => 0) (Set.uIcc a b) := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    simp [fE_eq_zero_of_ge (ha.trans ht.1)]
  rw [intervalIntegral.integral_congr this]; simp

lemma noiseCDF_fE (z : ℝ) : noiseCDF fE z = Φ (cl z) := by
  unfold noiseCDF
  rcases le_or_gt z (-8) with hz | hz
  · rw [cl_of_le hz]
    rw [setIntegral_eq_zero_of_forall_eq_zero]
    · simp [Φ]
    · intro t ht; exact fE_eq_zero_of_le (le_trans ht hz)
  · have h := intervalIntegral.integral_Iic_sub_Iic (μ := volume) (f := fE) (a := -8) (b := z)
      integrable_fE.integrableOn integrable_fE.integrableOn
    have h0 : ∫ x in Set.Iic (-8 : ℝ), fE x = 0 := by
      rw [setIntegral_eq_zero_of_forall_eq_zero]
      intro t ht; exact fE_eq_zero_of_le ht
    rw [h0, sub_zero] at h
    rw [h]
    rcases le_or_gt z 7 with hz7 | hz7
    · rw [intervalIntegral_fE hz.le hz7, cl_of_mem hz.le hz7]
    · rw [cl_of_ge hz7.le, ← intervalIntegral.integral_add_adjacent_intervals
        (b := 7) (continuous_fE.intervalIntegrable _ _) (continuous_fE.intervalIntegrable _ _),
        intervalIntegral_fE (by norm_num) le_rfl]
      have := intervalIntegral_zero_part (a := 7) (b := z) le_rfl hz7.le (fun _ => 1)
      simp only [one_mul] at this
      rw [this]; norm_num [Φ]

lemma standing : NoiseStanding 8 fE where
  pos := by norm_num
  nonneg := fE_nonneg
  zero_outside := by
    intro z hz
    simp only [Set.mem_Icc, not_and_or, not_le] at hz
    rcases hz with h | h
    · exact fE_eq_zero_of_le h.le
    · exact fE_eq_zero_of_ge (by linarith)
  continuousOn := continuous_fE.continuousOn
  mass_one := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
        (b := 7) (continuous_fE.intervalIntegrable _ _) (continuous_fE.intervalIntegrable _ _),
        intervalIntegral_fE (by norm_num) le_rfl]
    have := intervalIntegral_zero_part (a := 7) (b := 8) le_rfl (by norm_num) (fun _ => 1)
    simp only [one_mul] at this
    rw [this]; norm_num [Φ]
  mean_zero := by
    have hc : Continuous fun z : ℝ => z * fE z := continuous_id.mul continuous_fE
    rw [← intervalIntegral.integral_add_adjacent_intervals
        (b := 7) (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
    rw [intervalIntegral_zero_part (a := 7) (b := 8) le_rfl (by norm_num) (fun z => z)]
    have hcongr : Set.EqOn (fun z => z * fE z) (fun t => t * pE t) (Set.uIcc (-8) 7) := by
      intro t ht
      rw [Set.uIcc_of_le (by norm_num)] at ht
      simp only [fE, pE, cl_of_mem ht.1 ht.2]
    rw [intervalIntegral.integral_congr hcongr,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_Q t)
        ((by unfold pE; fun_prop : Continuous fun t => t * pE t).intervalIntegrable _ _)]
    norm_num

/-- weighted AM-GM in the form used below -/
lemma amgm {p q a b H : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hH : a * p + b * q ≤ H) : p ^ a * q ^ b ≤ H :=
  (Real.geom_mean_le_arith_mean2_weighted ha hb hp hq hab).trans hH

lemma Φ_logconcave {p q a b : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    Φ p ^ a * Φ q ^ b ≤ Φ (a * p + b * q) := by
  unfold Φ
  have hp2 : 0 ≤ 2 - p ^ 2 := by nlinarith
  have hq2 : 0 ≤ 2 - q ^ 2 := by nlinarith
  rw [Real.mul_rpow (by positivity) hp2, Real.mul_rpow (by positivity) hq2,
    ← Real.rpow_pow_comm hp0, ← Real.rpow_pow_comm hq0]
  have e1 : p ^ a * q ^ b ≤ a * p + b * q := amgm hp0 hq0 ha hb hab le_rfl
  have e2 : (2 - p ^ 2) ^ a * (2 - q ^ 2) ^ b ≤ 2 - (a * p + b * q) ^ 2 := by
    apply amgm hp2 hq2 ha hb hab
    have : b = 1 - a := by linarith
    subst this
    nlinarith [sq_nonneg (p - q), mul_nonneg ha hb]
  have e1' : (p ^ a * q ^ b) ^ 2 ≤ (a * p + b * q) ^ 2 :=
    pow_le_pow_left₀ (by positivity) e1 2
  calc (p ^ a) ^ 2 * (2 - p ^ 2) ^ a * ((q ^ b) ^ 2 * (2 - q ^ 2) ^ b)
      = (p ^ a * q ^ b) ^ 2 * ((2 - p ^ 2) ^ a * (2 - q ^ 2) ^ b) := by ring
    _ ≤ (a * p + b * q) ^ 2 * (2 - (a * p + b * q) ^ 2) :=
        mul_le_mul e1' e2 (by positivity) (by positivity)

lemma Ψ_logconcave {p q a b : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    Ψ p ^ a * Ψ q ^ b ≤ Ψ (a * p + b * q) := by
  unfold Ψ
  have hp2 : 0 ≤ 1 - p ^ 2 := by nlinarith
  have hq2 : 0 ≤ 1 - q ^ 2 := by nlinarith
  rw [← Real.rpow_pow_comm hp2, ← Real.rpow_pow_comm hq2, ← mul_pow]
  have e2 : (1 - p ^ 2) ^ a * (1 - q ^ 2) ^ b ≤ 1 - (a * p + b * q) ^ 2 := by
    apply amgm hp2 hq2 ha hb hab
    have : b = 1 - a := by linarith
    subst this
    nlinarith [sq_nonneg (p - q), mul_nonneg ha hb]
  exact pow_le_pow_left₀ (by positivity) e2 2

lemma Φ_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) : Φ u ≤ Φ v := by
  unfold Φ
  have h1 : u ^ 2 ≤ v ^ 2 := pow_le_pow_left₀ hu huv 2
  have h2 : u ^ 2 + v ^ 2 ≤ 2 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]

lemma cl_concave {x y a b : ℝ} (hx : -8 ≤ x) (hy : -8 ≤ y) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : a * cl x + b * cl y ≤ cl (a * x + b * y) := by
  have ex : cl x = min 1 ((x + 8) / 15) := by
    unfold cl; exact max_eq_right (le_min zero_le_one (by linarith))
  have ey : cl y = min 1 ((y + 8) / 15) := by
    unfold cl; exact max_eq_right (le_min zero_le_one (by linarith))
  rw [ex, ey]
  unfold cl
  apply le_max_of_le_right
  apply le_min
  · nlinarith [min_le_left 1 ((x + 8) / 15), min_le_left 1 ((y + 8) / 15)]
  · have h1 := mul_le_mul_of_nonneg_left (min_le_right 1 ((x + 8) / 15)) ha
    have h2 := mul_le_mul_of_nonneg_left (min_le_right 1 ((y + 8) / 15)) hb
    have : a * ((x + 8) / 15) + b * ((y + 8) / 15) = (a * x + b * y + 8) / 15 := by
      have : b = 1 - a := by linarith
      subst this; ring
    linarith

lemma assumption1 : Assumption1 8 fE := by
  have hF : ∀ z, noiseCDF fE z = Φ (cl z) := noiseCDF_fE
  have hS : ∀ z, 1 - noiseCDF fE z = Ψ (cl z) := by
    intro z; rw [hF]; unfold Φ Ψ; ring
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro z _; rw [hF]; unfold Φ
    have := cl_nonneg z; have := cl_le_one z
    apply mul_nonneg (by positivity); nlinarith
  · intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul, hF]
    calc Φ (cl x) ^ a * Φ (cl y) ^ b ≤ Φ (a * cl x + b * cl y) :=
          Φ_logconcave (cl_nonneg x) (cl_le_one x) (cl_nonneg y) (cl_le_one y) ha hb hab
      _ ≤ Φ (cl (a * x + b * y)) := by
          apply Φ_mono (by have := cl_nonneg x; have := cl_nonneg y; positivity)
            (cl_concave hx.1 hy.1 ha hb hab) (cl_le_one _)
  · intro z _; show 0 ≤ 1 - noiseCDF fE z; rw [hS]; unfold Ψ; positivity
  · intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul]
    rw [hS, hS, hS]
    have hΨ0 : ∀ u, 0 ≤ Ψ u := fun u => by unfold Ψ; positivity
    rcases eq_or_lt_of_le ha with ha0 | ha0
    · subst ha0
      have : b = 1 := by linarith
      subst this; simp
    rcases eq_or_lt_of_le hb with hb0 | hb0
    · subst hb0
      have : a = 1 := by linarith
      subst this; simp
    by_cases hx7 : 7 ≤ x
    · rw [cl_of_ge hx7]
      simp [Ψ, Real.zero_rpow ha0.ne']; positivity
    by_cases hy7 : 7 ≤ y
    · rw [cl_of_ge hy7]
      simp [Ψ, Real.zero_rpow hb0.ne']; positivity
    push Not at hx7 hy7
    have hxy1 : -8 ≤ a * x + b * y := by nlinarith [hx.1, hy.1]
    have hxy2 : a * x + b * y ≤ 7 := by nlinarith
    rw [cl_of_mem hx.1 hx7.le, cl_of_mem hy.1 hy7.le, cl_of_mem hxy1 hxy2]
    have e : (a * x + b * y + 8) / 15 = a * ((x + 8) / 15) + b * ((y + 8) / 15) := by
      have : b = 1 - a := by linarith
      subst this; ring
    rw [e]
    exact Ψ_logconcave (by linarith [hx.1]) (by linarith) (by linarith [hy.1]) (by linarith)
      ha hb hab

end CorpL2Counter

open CorpL2Counter in
theorem solution : ¬ (∀ (d : ℕ) (Bn : ℝ) (f : ℝ → ℝ)
    (hf : NoiseStanding Bn f) (hA1 : Assumption1 Bn f)
    (x β βhat : Ctx d) (hβ : -Bn < ⟪x, β⟫) (hβhat : -Bn < ⟪x, βhat⟫)
    (rStar r : ℝ) (hrStar : IsMaxOn (reserveObjective f ⟪x, β⟫) Set.univ rStar)
    (hr : IsMaxOn (reserveObjective f ⟪x, βhat⟫) Set.univ r),
    |rStar - r| ≤ |⟪x, β - βhat⟫|) := by
  intro H
  let x : Ctx 1 := EuclideanSpace.single 0 1
  let β : Ctx 1 := (-15 / 2 : ℝ) • x
  have hxx : ⟪x, x⟫ = 1 := by
    simp [x, real_inner_self_eq_norm_sq]
  have hθ : ⟪x, β⟫ = -15 / 2 := by
    simp only [β, real_inner_smul_right, hxx]; norm_num
  have hF1 : ∀ z, 7 ≤ z → noiseCDF fE z = 1 := by
    intro z hz; rw [noiseCDF_fE, cl_of_ge hz]; norm_num [Φ]
  have hFle : ∀ z, noiseCDF fE z ≤ 1 := by
    intro z; rw [noiseCDF_fE]; unfold Φ
    have := cl_nonneg z; have := cl_le_one z
    nlinarith [sq_nonneg (1 - cl z ^ 2)]
  have hmax : ∀ y0 : ℝ, 0 ≤ y0 → IsMaxOn (reserveObjective fE ⟪x, β⟫) Set.univ y0 := by
    intro y0 hy0 y _
    simp only [Set.mem_setOf_eq, reserveObjective, hθ]
    rw [hF1 (y0 - -15 / 2) (by linarith), sub_self, mul_zero]
    rcases le_or_gt y 0 with hy | hy
    · exact mul_nonpos_of_nonpos_of_nonneg hy (by linarith [hFle (y - -15 / 2)])
    · rw [hF1 (y - -15 / 2) (by linarith)]; simp
  have := H 1 8 fE standing assumption1 x β β (by rw [hθ]; norm_num) (by rw [hθ]; norm_num)
    0 1 (hmax 0 le_rfl) (hmax 1 zero_le_one)
  norm_num at this
