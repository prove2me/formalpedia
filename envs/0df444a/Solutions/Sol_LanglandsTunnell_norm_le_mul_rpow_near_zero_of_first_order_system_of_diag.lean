-- Prove2me | solution 1 for LanglandsTunnell.norm_le_mul_rpow_near_zero_of_first_order_system_of_diag
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/953566ff-8c70-5222-b9a9-675189e127b3

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.Pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_first_order_system_of_diag

set_option autoImplicit false

open scoped Real

namespace LanglandsTunnell
namespace OdeEAux

p2m_open "Real Set Finset Set.Finset"

theorem re_inner_le (z s a : ℂ) (r₀ : ℝ) (ha : r₀ ≤ a.re) :
    2 * (z.re * (((r₀ : ℂ) - a) * z - s).re + z.im * (((r₀ : ℂ) - a) * z - s).im) ≤ 2 * (‖z‖ * ‖s‖) := by
  have h1 : z.re * (((r₀ : ℂ) - a) * z - s).re + z.im * (((r₀ : ℂ) - a) * z - s).im =
      (r₀ - a.re) * (z.re ^ 2 + z.im ^ 2) - (z * (starRingEnd ℂ) s).re := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im]
    ring
  have h2 : (r₀ - a.re) * (z.re ^ 2 + z.im ^ 2) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have h3 : -(z * (starRingEnd ℂ) s).re ≤ ‖z‖ * ‖s‖ := by
    have h := Complex.abs_re_le_norm (z * (starRingEnd ℂ) s)
    rw [norm_mul, Complex.norm_conj] at h
    have := neg_abs_le (z * (starRingEnd ℂ) s).re
    linarith
  rw [h1]
  linarith

theorem main (m : ℕ) (a : Fin m → ℂ) (r₀ c τ : ℝ) (hτ : 0 < τ) (ha : ∀ i, r₀ ≤ (a i).re)
    (B : ℝ → Matrix (Fin m) (Fin m) ℂ) (hB : ∀ y : ℝ, 0 < y → y ≤ 1 → ∀ i j, ‖B y i j‖ ≤ c * y ^ τ)
    (F : Fin m → ℝ → ℂ) (hF : ∀ i, DifferentiableOn ℝ (F i) (Set.Ioi 0))
    (hFeq : ∀ y : ℝ, 0 < y → y ≤ 1 → ∀ i,
      (y : ℂ) * deriv (F i) y = a i * F i y + ∑ j, B y i j * F j y)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ∀ i, ‖F i y‖ ≤ C * y ^ (r₀ - ε) := by

  obtain ⟨c', hc'⟩ : ∃ c' : ℝ, c' = max c 0 := ⟨_, rfl⟩
  have hc'0 : 0 ≤ c' := hc' ▸ le_max_right _ _
  have hcc' : c ≤ c' := hc' ▸ le_max_left _ _
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = 2 * c' * m / τ := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by rw [hL]; positivity

  set G : Fin m → ℝ → ℂ := fun i t => Complex.exp ((r₀ : ℂ) * (t : ℂ)) * F i (Real.exp (-t)) with hG
  set G' : Fin m → ℝ → ℂ := fun i t =>
    ((r₀ : ℂ) - a i) * G i t - ∑ j, B (Real.exp (-t)) i j * G j t with hG'

  have hGraw : ∀ (i : Fin m) (t : ℝ), HasDerivAt (G i)
      (Complex.exp ((r₀ : ℂ) * (t : ℂ)) * (r₀ : ℂ) * F i (Real.exp (-t)) +
        Complex.exp ((r₀ : ℂ) * (t : ℂ)) * ((-Real.exp (-t)) • deriv (F i) (Real.exp (-t)))) t := by
    intro i t
    have hy : 0 < Real.exp (-t) := Real.exp_pos _
    have h1 : HasDerivAt (fun s : ℝ => Complex.exp ((r₀ : ℂ) * (s : ℂ))) (Complex.exp ((r₀ : ℂ) * (t : ℂ)) * (r₀ : ℂ)) t := by
      have h0 : HasDerivAt (fun s : ℝ => (r₀ : ℂ) * (s : ℂ)) (r₀ : ℂ) t := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (r₀ : ℂ)
      exact h0.cexp
    have h2 : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
      simpa using (hasDerivAt_neg t).exp
    have h3 : HasDerivAt (F i) (deriv (F i) (Real.exp (-t))) (Real.exp (-t)) :=
      ((hF i).differentiableAt (Ioi_mem_nhds hy)).hasDerivAt
    have h4 : HasDerivAt (fun s : ℝ => F i (Real.exp (-s))) ((-Real.exp (-t)) • deriv (F i) (Real.exp (-t))) t :=
      h3.scomp t h2
    exact h1.mul h4
  have hGder : ∀ (i : Fin m) (t : ℝ), 0 ≤ t → HasDerivAt (G i) (G' i t) t := by
    intro i t ht
    have hy : 0 < Real.exp (-t) := Real.exp_pos _
    have hy1 : Real.exp (-t) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    have key := hFeq (Real.exp (-t)) hy hy1 i
    refine (hGraw i t).congr_deriv ?_
    have hs : ∑ j, B (Real.exp (-t)) i j * G j t =
        Complex.exp ((r₀ : ℂ) * (t : ℂ)) * ∑ j, B (Real.exp (-t)) i j * F j (Real.exp (-t)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by simp only [hG]; ring
    simp only [hG', hs, Complex.real_smul, Complex.ofReal_neg]
    linear_combination (-Complex.exp ((r₀ : ℂ) * (t : ℂ))) * key
  have hGcont : ∀ i : Fin m, Continuous (G i) := fun i =>
    continuous_iff_continuousAt.2 fun t => (hGraw i t).continuousAt

  set E : ℝ → ℝ := fun t => ∑ i, ((G i t).re ^ 2 + (G i t).im ^ 2) with hE
  set E' : ℝ → ℝ := fun t => ∑ i, 2 * ((G i t).re * (G' i t).re + (G i t).im * (G' i t).im) with hE'
  have hEnorm : ∀ t, E t = ∑ i, ‖G i t‖ ^ 2 := fun t =>
    Finset.sum_congr rfl fun i _ => by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hEder : ∀ t : ℝ, 0 ≤ t → HasDerivAt E (E' t) t := by
    intro t ht
    have hterm : ∀ i ∈ Finset.univ, HasDerivAt (fun s => (G i s).re ^ 2 + (G i s).im ^ 2)
        (2 * ((G i t).re * (G' i t).re + (G i t).im * (G' i t).im)) t := by
      intro i _
      have hre : HasDerivAt (fun s => (G i s).re) (G' i t).re t := by
        have h__af := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hGder i t ht))
        simp at h__af
        exact h__af
      have him : HasDerivAt (fun s => (G i s).im) (G' i t).im t := by
        have h__af := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hGder i t ht))
        simp at h__af
        exact h__af
      have h := (hre.pow 2).add (him.pow 2)
      refine h.congr_deriv ?_
      push_cast
      ring
    have h := HasDerivAt.fun_sum hterm
    exact h
  have hEcont : Continuous E := by
    simp only [hE]
    refine continuous_finsetSum _ fun i _ => ?_
    exact ((Complex.continuous_re.comp (hGcont i)).pow 2).add ((Complex.continuous_im.comp (hGcont i)).pow 2)

  have hE'le : ∀ t : ℝ, 0 ≤ t → E' t ≤ (2 * c' * m * Real.exp (-(τ * t))) * E t := by
    intro t ht
    have hy : 0 < Real.exp (-t) := Real.exp_pos _
    have hy1 : Real.exp (-t) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    have hyτ : Real.exp (-t) ^ τ = Real.exp (-(τ * t)) := by rw [← Real.exp_mul]; ring_nf
    set S := ∑ j, ‖G j t‖ with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => norm_nonneg _

    have hsi : ∀ i, ‖∑ j, B (Real.exp (-t)) i j * G j t‖ ≤ c' * Real.exp (-(τ * t)) * S := by
      intro i
      calc ‖∑ j, B (Real.exp (-t)) i j * G j t‖ ≤ ∑ j, ‖B (Real.exp (-t)) i j * G j t‖ := norm_sum_le _ _
        _ ≤ ∑ j, (c' * Real.exp (-(τ * t))) * ‖G j t‖ := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [norm_mul]
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            have h := hB (Real.exp (-t)) hy hy1 i j
            rw [hyτ] at h
            exact h.trans (mul_le_mul_of_nonneg_right hcc' (Real.exp_pos _).le)
        _ = c' * Real.exp (-(τ * t)) * S := by rw [hS, Finset.mul_sum]
    have hcomp : ∀ i, 2 * ((G i t).re * (G' i t).re + (G i t).im * (G' i t).im) ≤
        2 * (‖G i t‖ * (c' * Real.exp (-(τ * t)) * S)) := by
      intro i
      have h := re_inner_le (G i t) (∑ j, B (Real.exp (-t)) i j * G j t) (a i) r₀ (ha i)
      refine h.trans ?_
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hsi i) (norm_nonneg _)) (by norm_num)
    calc E' t = ∑ i, 2 * ((G i t).re * (G' i t).re + (G i t).im * (G' i t).im) := rfl
      _ ≤ ∑ i, 2 * (‖G i t‖ * (c' * Real.exp (-(τ * t)) * S)) := Finset.sum_le_sum fun i _ => hcomp i
      _ = 2 * c' * Real.exp (-(τ * t)) * S ^ 2 := by
          rw [← Finset.mul_sum, ← Finset.sum_mul, ← hS]; ring
      _ ≤ 2 * c' * Real.exp (-(τ * t)) * (m * E t) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [hEnorm t, hS]
          simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => ‖G j t‖))
      _ = (2 * c' * m * Real.exp (-(τ * t))) * E t := by ring

  set Φ : ℝ → ℝ := fun t => L * (1 - Real.exp (-(τ * t))) with hΦ
  set W : ℝ → ℝ := fun t => Real.exp (-Φ t) * E t with hW
  set W' : ℝ → ℝ := fun t => Real.exp (-Φ t) * (E' t - (2 * c' * m * Real.exp (-(τ * t))) * E t) with hW'
  have hΦder : ∀ t, HasDerivAt Φ (2 * c' * m * Real.exp (-(τ * t))) t := by
    intro t
    have h0 : HasDerivAt (fun s : ℝ => -(τ * s)) (-τ) t := by
      have h__af := ((hasDerivAt_id t).const_mul τ).neg
      simp at h__af
      exact h__af
    have h1 := ((h0.exp).const_sub 1).const_mul L
    refine h1.congr_deriv ?_
    rw [hL]; field_simp
  have hWder : ∀ t, 0 ≤ t → HasDerivAt W (W' t) t := by
    intro t ht
    have h1 : HasDerivAt (fun s => Real.exp (-Φ s)) (Real.exp (-Φ t) * -(2 * c' * m * Real.exp (-(τ * t)))) t :=
      (hΦder t).neg.exp
    have h := h1.mul (hEder t ht)
    refine h.congr_deriv ?_
    simp only [hW']
    ring
  have hWcont : Continuous W := by
    have hΦc : Continuous Φ := continuous_iff_continuousAt.2 fun t => (hΦder t).continuousAt
    exact (Real.continuous_exp.comp hΦc.neg).mul hEcont
  have hW'le : ∀ t, 0 ≤ t → W' t ≤ 0 := by
    intro t ht
    have h := hE'le t ht
    have : E' t - (2 * c' * m * Real.exp (-(τ * t))) * E t ≤ 0 := by linarith
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le this
  have hW0 : W 0 = E 0 := by simp [hW, hΦ]

  refine ⟨Real.sqrt (E 0 * Real.exp L), fun y hy hy1 i => ?_⟩
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = -Real.log y := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := by rw [hT]; have := Real.log_nonpos hy.le hy1; linarith
  have hfence := image_le_of_deriv_right_le_deriv_boundary (f := W) (f' := W') (a := 0) (b := T)
    hWcont.continuousOn (fun t ht => (hWder t ht.1).hasDerivWithinAt)
    (B := fun _ => E 0) (B' := fun _ => 0) (by rw [hW0]) continuousOn_const
    (fun t _ => (hasDerivAt_const t (E 0)).hasDerivWithinAt) (fun t ht => hW'le t ht.1) (x := T) ⟨hT0, le_rfl⟩

  have hE0 : 0 ≤ E 0 := by rw [hEnorm]; exact Finset.sum_nonneg fun i _ => by positivity
  have hΦT : Φ T ≤ L := by
    simp only [hΦ]
    have : 0 ≤ Real.exp (-(τ * T)) := (Real.exp_pos _).le
    nlinarith
  have hET : E T ≤ E 0 * Real.exp L := by
    have h1 : Real.exp (-Φ T) * E T ≤ E 0 := hfence
    have h2 : E T = Real.exp (Φ T) * (Real.exp (-Φ T) * E T) := by
      rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
    rw [h2]
    calc Real.exp (Φ T) * (Real.exp (-Φ T) * E T) ≤ Real.exp (Φ T) * E 0 :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ ≤ Real.exp L * E 0 := mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hΦT) hE0
      _ = E 0 * Real.exp L := mul_comm _ _

  have hGi : ‖G i T‖ ^ 2 ≤ E 0 * Real.exp L := by
    have h1 : ‖G i T‖ ^ 2 ≤ E T := by
      rw [hEnorm]
      exact Finset.single_le_sum (f := fun j => ‖G j T‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)
    exact h1.trans hET
  have hGi' : ‖G i T‖ ≤ Real.sqrt (E 0 * Real.exp L) := by
    rw [← Real.sqrt_sq (norm_nonneg (G i T))]
    exact Real.sqrt_le_sqrt hGi

  have e1 : Real.exp (-T) = y := by rw [hT, neg_neg, Real.exp_log hy]
  have e2 : Real.exp (r₀ * T) = y ^ (-r₀) := by
    rw [Real.rpow_def_of_pos hy, hT]; congr 1; ring
  have hre : ((r₀ : ℂ) * (T : ℂ)).re = r₀ * T := by simp [Complex.mul_re]
  have hGT : ‖G i T‖ = y ^ (-r₀) * ‖F i y‖ := by
    simp only [hG, norm_mul, Complex.norm_exp, hre, e1, e2]
  rw [hGT] at hGi'
  have hyρ : 0 < y ^ r₀ := Real.rpow_pos_of_pos hy _
  have hsplit : ‖F i y‖ = y ^ r₀ * (y ^ (-r₀) * ‖F i y‖) := by
    rw [Real.rpow_neg hy.le, ← mul_assoc, mul_inv_cancel₀ hyρ.ne', one_mul]
  rw [hsplit]
  calc y ^ r₀ * (y ^ (-r₀) * ‖F i y‖) ≤ y ^ r₀ * Real.sqrt (E 0 * Real.exp L) :=
        mul_le_mul_of_nonneg_left hGi' hyρ.le
    _ = Real.sqrt (E 0 * Real.exp L) * y ^ r₀ := mul_comm _ _
    _ ≤ Real.sqrt (E 0 * Real.exp L) * y ^ (r₀ - ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hy hy1 (by linarith)) (Real.sqrt_nonneg _)

end LanglandsTunnell.OdeEAux

theorem solution
    (m : ℕ) (a : Fin m → ℂ) (r₀ c τ : ℝ) (hτ : 0 < τ) (ha : ∀ i, r₀ ≤ (a i).re)
    (B : ℝ → Matrix (Fin m) (Fin m) ℂ) (hB : ∀ y : ℝ, 0 < y → y ≤ 1 → ∀ i j, ‖B y i j‖ ≤ c * y ^ τ)
    (F : Fin m → ℝ → ℂ) (hF : ∀ i, DifferentiableOn ℝ (F i) (Set.Ioi 0))
    (hFeq : ∀ y : ℝ, 0 < y → y ≤ 1 → ∀ i,
      (y : ℂ) * deriv (F i) y = a i * F i y + ∑ j, B y i j * F j y) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ∀ i, ‖F i y‖ ≤ C * y ^ (r₀ - ε) := by
  intro ε hε
  exact LanglandsTunnell.OdeEAux.main m a r₀ c τ hτ ha B hB F hF hFeq ε hε

end S_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_first_order_system_of_diag
end P2MW
export P2MW.S_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_first_order_system_of_diag (solution)
