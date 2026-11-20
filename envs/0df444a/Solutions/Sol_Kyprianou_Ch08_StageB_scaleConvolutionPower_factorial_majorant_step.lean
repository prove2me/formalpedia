-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.scaleConvolutionPower_factorial_majorant_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T00:16:22.145449+00:00
-- url     : https://prove2.me/submissions/bdd58032-651e-4f4e-a971-e54d5be181fa

import Mathlib
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_integral_backward_power_Ioc
set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08.StageB Set

theorem solution (W : ℝ → ℝ)
    (hpos : ∀ x : ℝ, 0 ≤ x → 0 ≤ W x)
    (hmono : MonotoneOn W (Set.Ici (0 : ℝ)))
    (n : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (hint : IntegrableOn (fun s : ℝ => W s * scaleConvolutionPower W n (x - s))
      (Set.Ioc (0 : ℝ) x) volume)
    (hih : ∀ y : ℝ, 0 ≤ y →
      scaleConvolutionPower W n y ≤
        (y ^ n / (Nat.factorial n : ℝ)) * W y ^ (n + 1)) :
    scaleConvolutionPower W (n + 1) x ≤
      (x ^ (n + 1) / (Nat.factorial (n + 1) : ℝ)) * W x ^ (n + 2) := by
  let C : ℝ := W x * W x ^ (n + 1) / (Nat.factorial n : ℝ)
  have hfc : (0 : ℝ) < (Nat.factorial n : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  have hpoint : ∀ s : ℝ, s ∈ Set.Ioc (0 : ℝ) x →
      W s * scaleConvolutionPower W n (x - s) ≤ (x - s) ^ n * C := by
    intro s hs
    have hspos : 0 ≤ s := hs.1.le
    have hdiff : 0 ≤ x - s := sub_nonneg.mpr hs.2
    have hsBound : W s ≤ W x :=
      hmono hspos hx hs.2
    have hdBound : W (x - s) ≤ W x :=
      hmono hdiff hx (sub_le_self x hspos)
    have hpow : W (x - s) ^ (n + 1) ≤ W x ^ (n + 1) := by
      gcongr
      exact hpos (x - s) hdiff
    have hcoef : 0 ≤ (x - s)^n / (Nat.factorial n : ℝ) :=
      div_nonneg (pow_nonneg hdiff n) (le_of_lt hfc)
    have hrec : scaleConvolutionPower W n (x - s) ≤
        (x - s)^n / (Nat.factorial n : ℝ) * W x ^ (n + 1) :=
      (hih (x - s) hdiff).trans (mul_le_mul_of_nonneg_left hpow hcoef)
    have hmajor : 0 ≤ (x - s)^n / (Nat.factorial n : ℝ) * W x^(n + 1) :=
      mul_nonneg hcoef (pow_nonneg (hpos x hx) (n + 1))
    calc
      W s * scaleConvolutionPower W n (x - s) ≤
          W s * ((x - s)^n / (Nat.factorial n : ℝ) * W x^(n + 1)) :=
        mul_le_mul_of_nonneg_left hrec (hpos s hspos)
      _ ≤ W x * ((x - s)^n / (Nat.factorial n : ℝ) * W x^(n + 1)) :=
        mul_le_mul_of_nonneg_right hsBound hmajor
      _ = (x - s)^n * C := by
        dsimp [C]
        ring
  have hucont : Continuous (fun s : ℝ => (x - s)^n * C) :=
    ((continuous_const.sub continuous_id).pow n).mul continuous_const
  have huintegrable : Integrable
      (fun s : ℝ => (x - s)^n * C) (volume.restrict (Set.Ioc (0 : ℝ) x)) :=
    hucont.integrableOn_Ioc
  have hI : (∫ s in Set.Ioc (0 : ℝ) x,
       W s * scaleConvolutionPower W n (x - s) ∂volume) ≤
      (∫ s in Set.Ioc (0 : ℝ) x, (x - s)^n * C ∂volume) := by
    apply integral_mono_ae hint huintegrable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hpoint s hs
  have hcalc : (∫ s in Set.Ioc (0 : ℝ) x, (x - s)^n * C ∂volume) =
      (x^(n+1) / (n+1)) * C := by
    rw [integral_mul_const]
    rw [integral_backward_power_Ioc x n hx]
  calc
    scaleConvolutionPower W (n + 1) x =
        ∫ s in Set.Ioc (0 : ℝ) x,
          W s * scaleConvolutionPower W n (x - s) ∂volume := rfl
    _ ≤ (∫ s in Set.Ioc (0 : ℝ) x, (x - s)^n * C ∂volume) := hI
    _ = (x^(n+1) / (n+1)) * C := hcalc
    _ = (x^(n+1) / (Nat.factorial (n+1) : ℝ)) * W x^(n+2) := by
      dsimp [C]
      rw [Nat.factorial_succ]
      push_cast
      rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
      have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
      have hf : (Nat.factorial n : ℝ) ≠ 0 := ne_of_gt hfc
      field_simp [hn, hf]
      ring
