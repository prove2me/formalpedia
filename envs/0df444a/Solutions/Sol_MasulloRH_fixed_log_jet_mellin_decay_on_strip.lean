-- Prove2me | solution 1 for MasulloRH.fixed_log_jet_mellin_decay_on_strip
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-21T04:41:06.149093+00:00
-- url     : https://prove2.me/submissions/de938ff5-34ac-4130-990c-a061624f9508

import Theorems.Thm_MasulloGRH_mellin_uniform_riemann_lebesgue
import Definitions.Def_MasulloRH_RationalTrace

open MeasureTheory MasulloGRH MasulloRH Set
open scoped ContDiff

theorem solution (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ)
    (a b : ℝ) (hab : a < b) (d N : ℕ) (hN : 1 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∃ Y : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → Y ≤ |s.im| →
      ‖∫ y : ℝ, φ (Real.exp y) * (y:ℂ)^d * Complex.exp (s*y)‖ ≤ C/|s.im|^N := by
  let ψ := fun t : ℝ => φ t * (Real.log t : ℂ)^d
  have hc : HasCompactSupport (fun x : ℝ => φ (Real.exp x)) := by
    apply HasCompactSupport.intro (K := Real.log '' tsupport φ)
    · exact hφ.2.1.image_of_continuousOn (Real.continuousOn_log.mono (fun t ht =>
        ne_of_gt (hφ.2.2.1 ht)))
    · intro x hx
      apply image_eq_zero_of_notMem_tsupport
      intro h
      exact hx ⟨_, h, Real.log_exp x⟩
  have hs : ContDiff ℝ ∞ (fun x : ℝ => φ (Real.exp x)) := hφ.1.comp Real.contDiff_exp
  have hcast : ContDiff ℝ ∞ ((↑) : ℝ → ℂ) := Complex.ofRealCLM.contDiff
  have hψ : IsSchwartzRpos ψ := by
    let g := fun y : ℝ => φ (Real.exp y) * (y:ℂ)^d
    have hg : HasCompactSupport g := hc.mul_right
    have hgs : ContDiff ℝ ∞ g := hs.mul (hcast.pow d)
    exact ⟨hg.toSchwartzMap hgs, fun x => by simp [g, ψ]⟩
  have hpow (σ : ℝ) : IsSchwartzRpos (powMul σ ψ) := by
    let g := fun y : ℝ => (Real.exp (y*σ) : ℂ) * (φ (Real.exp y) * (y:ℂ)^d)
    have hg : HasCompactSupport g := hc.mul_right.mul_left
    have hgs : ContDiff ℝ ∞ g := (hcast.comp (Real.contDiff_exp.comp (contDiff_id.mul contDiff_const))).mul
      (hs.mul (hcast.pow d))
    exact ⟨hg.toSchwartzMap hgs, fun x => by simp [g, ψ, powMul, Real.exp_mul]⟩
  obtain ⟨C, hC, Y, hY⟩ := (mellin_uniform_riemann_lebesgue a b hab ψ hψ
    (fun σ _ _ => hpow σ)).2.2.2 N hN
  refine ⟨C, hC, Y, fun s ha hb hy => ?_⟩
  have heq : mellin ψ s = ∫ y : ℝ, φ (Real.exp y) * (y:ℂ)^d * Complex.exp (s*y) := by
    have him : Real.exp '' (univ : Set ℝ) = Ioi 0 := by rw [image_univ, Real.range_exp]
    rw [mellin, ← him, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn,
      setIntegral_univ]
    apply integral_congr_ae
    filter_upwards with x
    simp only [abs_of_pos (Real.exp_pos _), smul_eq_mul, ψ, Real.log_exp]
    rw [Complex.real_smul, Complex.cpow_def_of_ne_zero (by exact_mod_cast Real.exp_ne_zero x)]
    rw [← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, Complex.ofReal_exp]
    rw [mul_left_comm, ← mul_assoc, ← Complex.exp_add]
    ring_nf
  rw [← heq]
  exact hY s ha hb hy
