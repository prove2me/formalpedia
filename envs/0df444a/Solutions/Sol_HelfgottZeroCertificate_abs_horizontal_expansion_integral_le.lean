-- Prove2me | solution 1 for HelfgottZeroCertificate.abs_horizontal_expansion_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @flyingviper
-- created : 2026-11-18T12:00:43.613369+00:00
-- url     : https://prove2.me/submissions/ce71cfc6-d592-465f-a6de-89fd04d0516e

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace HelfgottZeroCertificate
open Complex MeasureTheory Set

theorem horizontal_pole_im_integral {a b c d : ℝ} (hd : d≠0) :
    (∫ x in a..b, ((⟨x-c,d⟩:ℂ)⁻¹).im) =
      Real.arctan ((a-c)/d)-Real.arctan ((b-c)/d) := by
  have hden (x : ℝ) : (x-c)^2+d^2≠0 := ne_of_gt (by positivity)
  have he (x : ℝ) : ((⟨x-c,d⟩:ℂ)⁻¹).im = -d/((x-c)^2+d^2) := by
    rw [Complex.inv_im,Complex.normSq_apply]
    dsimp
    ring
  have hdv x : HasDerivAt (fun x : ℝ => -Real.arctan ((x-c)/d))
      (((⟨x-c,d⟩:ℂ)⁻¹).im) x := by
    have h := (((hasDerivAt_id x).sub_const c).div_const d).arctan.neg
    convert! h using 1
    rw [he]
    simp only [id_eq]
    field_simp
    <;> ring
  have hc : Continuous (fun x : ℝ => ((⟨x-c,d⟩:ℂ)⁻¹).im) := by
    simp_rw [he]
    exact continuous_const.div (((continuous_id.sub continuous_const).pow 2).add continuous_const) hden
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hdv x) (hc.intervalIntegrable a b)
  convert! hi using 1 <;> ring

/-- The horizontal argument change contributed by a single pole is at most pi. -/
theorem abs_horizontal_pole_im_integral_le_pi (a b : ℝ) (ρ : ℂ) (v : ℝ) :
    |∫ x in a..b, (((⟨x,v⟩:ℂ)-ρ)⁻¹).im| ≤ Real.pi := by
  have he x : (⟨x,v⟩:ℂ)-ρ=(⟨x-ρ.re,v-ρ.im⟩:ℂ) := by apply Complex.ext <;> rfl
  simp_rw [he]
  by_cases hd : v-ρ.im=0
  · simp [hd,Complex.inv_im,Real.pi_pos.le]
  · rw [horizontal_pole_im_integral hd]
    exact abs_le.mpr ⟨by linarith [Real.arctan_lt_pi_div_two ((b-ρ.re)/(v-ρ.im)),
      Real.neg_pi_div_two_lt_arctan ((a-ρ.re)/(v-ρ.im))],
      by linarith [Real.arctan_lt_pi_div_two ((a-ρ.re)/(v-ρ.im)),
      Real.neg_pi_div_two_lt_arctan ((b-ρ.re)/(v-ρ.im))]⟩

theorem horizontal_pole_im_continuous (ρ : ℂ) (v : ℝ) :
    Continuous (fun x : ℝ => (((⟨x,v⟩:ℂ)-ρ)⁻¹).im) := by
  by_cases hd : v-ρ.im=0
  · have he : (fun x : ℝ => (((⟨x,v⟩:ℂ)-ρ)⁻¹).im) = fun _ => (0:ℝ) := by
      funext x
      simp [Complex.inv_im,Complex.sub_im,hd]
    rw [he]
    exact continuous_const
  · have hc : Continuous (fun x : ℝ => (⟨x,v⟩:ℂ)-ρ) := by
      have he : (fun x : ℝ => (⟨x,v⟩:ℂ)-ρ) = fun x : ℝ => (x:ℂ)+(v:ℂ)*I-ρ := by
        funext x
        apply Complex.ext <;> simp
      rw [he]
      fun_prop
    exact Complex.continuous_im.comp (hc.inv₀ (fun x h => hd (by simpa using congrArg Complex.im h)))

theorem abs_horizontal_pole_sum_im_integral_le (S : Finset ℂ) (m : ℂ → ℝ)
    (hm : ∀ρ∈S,0≤m ρ) (a b v : ℝ) :
    |∫ x in a..b, ∑ρ∈S,m ρ*(((⟨x,v⟩:ℂ)-ρ)⁻¹).im| ≤
      Real.pi*(∑ρ∈S,m ρ) := by
  rw [intervalIntegral.integral_finsetSum (fun ρ _ =>
    ((horizontal_pole_im_continuous ρ v).const_mul (m ρ)).intervalIntegrable a b)]
  calc
    _ ≤ ∑ρ∈S,|∫x in a..b,m ρ*(((⟨x,v⟩:ℂ)-ρ)⁻¹).im| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ρ∈S,m ρ*Real.pi := by
      apply Finset.sum_le_sum
      intro ρ hρ
      rw [intervalIntegral.integral_const_mul,abs_mul,abs_of_nonneg (hm ρ hρ)]
      exact mul_le_mul_of_nonneg_left (abs_horizontal_pole_im_integral_le_pi a b ρ v) (hm ρ hρ)
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro ρ _; ring

/-- Integration of a finite local pole expansion with a uniformly bounded remainder. -/
theorem abs_horizontal_expansion_integral_le (S : Finset ℂ) (m : ℂ → ℝ)
    (hm : ∀ρ∈S,0≤m ρ) (a b v C : ℝ) (F : ℝ → ℝ)
    (hF : IntervalIntegrable F volume a b)
    (hrem : ∀x∈uIcc a b,|F x-∑ρ∈S,m ρ*(((⟨x,v⟩:ℂ)-ρ)⁻¹).im|≤C) :
    |∫x in a..b,F x| ≤ Real.pi*(∑ρ∈S,m ρ)+C*|b-a| := by
  let P : ℝ → ℝ := fun x => ∑ρ∈S,m ρ*(((⟨x,v⟩:ℂ)-ρ)⁻¹).im
  have hP : IntervalIntegrable P volume a b := by
    convert! (IntervalIntegrable.sum (μ:=volume) S (fun ρ _ =>
      ((horizontal_pole_im_continuous ρ v).const_mul (m ρ)).intervalIntegrable a b)) using 1
    funext x
    simp [P]
  have he : (∫x in a..b,F x) = (∫x in a..b,P x)+(∫x in a..b,F x-P x) := by
    rw [intervalIntegral.integral_sub hF hP]
    ring
  rw [he]
  apply (abs_add_le _ _).trans
  apply add_le_add (abs_horizontal_pole_sum_im_integral_le S m hm a b v)
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun x hx => show ‖F x-P x‖≤C from hrem x (Set.uIoc_subset_uIcc hx))
  simpa only [Real.norm_eq_abs] using hh

end HelfgottZeroCertificate

open Complex MeasureTheory Set
open scoped BigOperators
theorem solution :
∀ (S : Finset ℂ) (m : ℂ → ℝ),
  (∀ ρ ∈ S, 0 ≤ m ρ) →
    ∀ (a b v C : ℝ) (F : ℝ → ℝ),
      IntervalIntegrable F MeasureTheory.volume a b →
        (∀ x ∈ Set.uIcc a b, |F x - ∑ ρ ∈ S, m ρ * ({ re := x, im := v } - ρ)⁻¹.im| ≤ C) →
          |∫ (x : ℝ) in a..b, F x| ≤ Real.pi * ∑ ρ ∈ S, m ρ + C * |b - a| := @HelfgottZeroCertificate.abs_horizontal_expansion_integral_le
