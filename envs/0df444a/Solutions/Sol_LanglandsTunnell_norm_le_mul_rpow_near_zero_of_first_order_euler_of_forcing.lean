-- Prove2me | solution 1 for LanglandsTunnell.norm_le_mul_rpow_near_zero_of_first_order_euler_of_forcing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/f3594c8f-a388-5a09-a61e-344d1df2a46b

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_first_order_euler_of_forcing

set_option autoImplicit false

open scoped Real

namespace LanglandsTunnell
namespace OdeCAux

open Real Set

theorem main (b : ℂ) (σ A : ℝ) (f h : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0))
    (hh : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖h y‖ ≤ A * y ^ σ)
    (hfeq : ∀ y : ℝ, 0 < y → (y : ℂ) * deriv f y = b * f y + h y)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C * y ^ (min b.re σ - ε) := by
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = b.re - min b.re σ + ε := ⟨_, rfl⟩
  have hδpos : 0 < δ := by have := min_le_left b.re σ; linarith
  have hρσδ : b.re - σ ≤ δ := by have := min_le_right b.re σ; linarith
  obtain ⟨A', hA'⟩ : ∃ A' : ℝ, A' = max A 0 := ⟨_, rfl⟩
  have hA'0 : 0 ≤ A' := hA' ▸ le_max_right _ _
  have hAA' : A ≤ A' := hA' ▸ le_max_left _ _
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ, C₀ = ‖f 1‖ + A' / δ := ⟨_, rfl⟩
  have hC₀0 : 0 ≤ C₀ := by rw [hC₀]; positivity

  set G : ℝ → ℂ := fun t => Complex.exp (b * (t : ℂ)) * f (Real.exp (-t)) with hG
  set G' : ℝ → ℂ := fun t => -(Complex.exp (b * (t : ℂ)) * h (Real.exp (-t))) with hG'
  have hGder : ∀ t : ℝ, HasDerivAt G (G' t) t := by
    intro t
    have hy : 0 < Real.exp (-t) := Real.exp_pos _
    have h1 : HasDerivAt (fun s : ℝ => Complex.exp (b * (s : ℂ))) (Complex.exp (b * (t : ℂ)) * b) t := by
      have h0 : HasDerivAt (fun s : ℝ => b * (s : ℂ)) b t := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul b
      exact h0.cexp
    have h2 : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
      simpa using (hasDerivAt_neg t).exp
    have h3 : HasDerivAt f (deriv f (Real.exp (-t))) (Real.exp (-t)) :=
      (hf.differentiableAt (Ioi_mem_nhds hy)).hasDerivAt
    have h4 : HasDerivAt (fun s : ℝ => f (Real.exp (-s))) ((-Real.exp (-t)) • deriv f (Real.exp (-t))) t :=
      h3.scomp t h2
    have key := hfeq (Real.exp (-t)) hy
    refine (h1.mul h4).congr_deriv ?_
    simp only [hG', Complex.real_smul, Complex.ofReal_neg]
    linear_combination (-Complex.exp (b * (t : ℂ))) * key

  set B : ℝ → ℝ := fun t => C₀ * Real.exp (δ * t) with hB
  set B' : ℝ → ℝ := fun t => C₀ * (Real.exp (δ * t) * δ) with hB'
  have hBder : ∀ t : ℝ, HasDerivAt B (B' t) t := by
    intro t
    have h0 : HasDerivAt (fun s : ℝ => δ * s) δ t := by simpa using (hasDerivAt_id t).const_mul δ
    exact h0.exp.const_mul C₀
  have hG0 : G 0 = f 1 := by simp [hG]

  have hbound : ∀ t : ℝ, 0 ≤ t → ‖G' t‖ ≤ B' t := by
    intro t ht
    have hy : 0 < Real.exp (-t) := Real.exp_pos _
    have hy1 : Real.exp (-t) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    have hre : (b * (t : ℂ)).re = b.re * t := by simp [Complex.mul_re]
    have hnorm : ‖G' t‖ = Real.exp (b.re * t) * ‖h (Real.exp (-t))‖ := by
      simp only [hG', norm_neg, norm_mul, Complex.norm_exp, hre]
    have hh' : ‖h (Real.exp (-t))‖ ≤ A' * Real.exp (-t * σ) := by
      have h1 := hh (Real.exp (-t)) hy hy1
      rw [← Real.exp_mul] at h1
      exact h1.trans (mul_le_mul_of_nonneg_right hAA' (Real.exp_pos _).le)
    have hC₀B' : B' t = (‖f 1‖ * δ + A') * Real.exp (δ * t) := by
      simp only [hB']
      rw [hC₀]
      field_simp
    calc ‖G' t‖ = Real.exp (b.re * t) * ‖h (Real.exp (-t))‖ := hnorm
      _ ≤ Real.exp (b.re * t) * (A' * Real.exp (-t * σ)) :=
          mul_le_mul_of_nonneg_left hh' (Real.exp_pos _).le
      _ = A' * Real.exp ((b.re - σ) * t) := by
          rw [show (b.re - σ) * t = b.re * t + -t * σ by ring, Real.exp_add]; ring
      _ ≤ A' * Real.exp (δ * t) := by
          apply mul_le_mul_of_nonneg_left _ hA'0
          exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hρσδ ht)
      _ ≤ (‖f 1‖ * δ + A') * Real.exp (δ * t) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          have : 0 ≤ ‖f 1‖ * δ := mul_nonneg (norm_nonneg _) hδpos.le
          linarith
      _ = B' t := hC₀B'.symm
  refine ⟨C₀, fun y hy hy1 => ?_⟩
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = -Real.log y := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := by rw [hT]; have := Real.log_nonpos hy.le hy1; linarith
  have hfence := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := T)
    (fun t _ => (hGder t).continuousAt.continuousWithinAt)
    (fun t _ => (hGder t).hasDerivWithinAt)
    (B := B) (B' := B') (by rw [hG0]; simp only [hB, mul_zero, Real.exp_zero, mul_one, hC₀]; linarith [div_nonneg hA'0 hδpos.le])
    hBder (fun t ht => hbound t ht.1) (x := T) ⟨hT0, le_rfl⟩

  have e1 : Real.exp (-T) = y := by rw [hT, neg_neg, Real.exp_log hy]
  have e2 : ∀ c : ℝ, Real.exp (c * T) = y ^ (-c) := fun c => by
    rw [Real.rpow_def_of_pos hy, hT]; congr 1; ring
  have hre : (b * (T : ℂ)).re = b.re * T := by simp [Complex.mul_re]
  have hGT : ‖G T‖ = y ^ (-b.re) * ‖f y‖ := by
    simp only [hG, norm_mul, Complex.norm_exp, hre, e1, e2]
  have hBT : B T = C₀ * y ^ (-δ) := by simp only [hB, e2]
  rw [hGT, hBT] at hfence
  have hyρ : 0 < y ^ b.re := Real.rpow_pos_of_pos hy _
  have hsplit : ‖f y‖ = y ^ b.re * (y ^ (-b.re) * ‖f y‖) := by
    rw [Real.rpow_neg hy.le, ← mul_assoc, mul_inv_cancel₀ hyρ.ne', one_mul]
  rw [hsplit]
  calc y ^ b.re * (y ^ (-b.re) * ‖f y‖) ≤ y ^ b.re * (C₀ * y ^ (-δ)) :=
        mul_le_mul_of_nonneg_left hfence hyρ.le
    _ = C₀ * (y ^ b.re * y ^ (-δ)) := by ring
    _ = C₀ * y ^ (min b.re σ - ε) := by
        rw [← Real.rpow_add hy]
        congr 2
        rw [hδ]; ring

end LanglandsTunnell.OdeCAux

theorem solution
    (b : ℂ) (σ A : ℝ) (f h : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0))
    (hh : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖h y‖ ≤ A * y ^ σ)
    (hfeq : ∀ y : ℝ, 0 < y → (y : ℂ) * deriv f y = b * f y + h y) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C * y ^ (min b.re σ - ε) := by
  intro ε hε
  exact LanglandsTunnell.OdeCAux.main b σ A f h hf hh hfeq ε hε

end S_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_first_order_euler_of_forcing
end P2MW
export P2MW.S_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_first_order_euler_of_forcing (solution)
