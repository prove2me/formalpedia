-- Prove2me | solution 1 for MasulloRH.trace_strip_reflection_equiv_mathlib
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-22T02:32:33.288033+00:00
-- url     : https://prove2.me/submissions/1dc6d361-6ed6-4317-b180-2219eaa82bef

import Definitions.Def_MasulloRH_RationalTrace
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

set_option autoImplicit false
open MeasureTheory Set
open scoped Topology ContDiff
open MasulloRH

theorem solution (α : ℝ) :
    ∃ e : ZetaZerosInTraceStrip α ≃ ZetaZerosInTraceStrip α,
      ∀ ρ, (e ρ).val = 1 - ρ.val := by
  have hcos_strip : ∀ s : ℂ, 0 < s.re → s.re < 1 →
      Complex.cos ((Real.pi : ℂ) * s / 2) ≠ 0 := by
    intro s h0 h1
    rw [Complex.cos_ne_zero_iff]
    intro k hk
    have hr := congrArg Complex.re hk
    have hi := congrArg Complex.im hk
    norm_num [Complex.mul_re, Complex.div_re, Complex.add_re, Complex.sub_re,
      Complex.natCast_re, Complex.intCast_re] at hr hi
    have hp : 0 < Real.pi := Real.pi_pos
    have hkeq : s.re = (2 * (k : ℝ) + 1) := by
      nlinarith [hr]
    have hk0 : (k : ℝ) < 0 := by
      by_contra hn
      have hkge : (0 : ℝ) ≤ k := le_of_not_gt hn
      nlinarith [hkeq]
    have hklt : k < 0 := by exact_mod_cast hk0
    have hkneg : (k : ℝ) ≤ -1 := by
      have hkneg_int : k ≤ -1 := by omega
      exact_mod_cast hkneg_int
    nlinarith [hkeq]
  have hnotneg : ∀ s : ℂ, 0 < s.re → ∀ n : ℕ, s ≠ -(n : ℂ) := by
    intro s hs n heq
    have hre := congrArg Complex.re heq
    norm_num at hre
    linarith
  have hnotone : ∀ s : ℂ, s.re < 1 → s ≠ 1 := by
    intro s hs heq
    have hre := congrArg Complex.re heq
    norm_num at hre
    linarith
  have hreflect : ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 →
      riemannZeta (1 - s) = 0 := by
    intro s hs0 hs1 hzero
    let b : ℂ := 2 * (Real.pi : ℂ)
    have hb : b ≠ 0 := by
      simp [b, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
    have hpow0 : b ^ (-s) ≠ 0 := by
      intro hz
      exact hb ((Complex.cpow_eq_zero_iff b (-s)).mp hz).1
    have hgamma0 : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero (hnotneg s hs0)
    have hcos0 := hcos_strip s hs0 hs1
    have hunit : 2 * b ^ (-s) * Complex.Gamma s *
        Complex.cos ((Real.pi : ℂ) * s / 2) ≠ 0 := by
      simp [hpow0, hgamma0, hcos0]
    calc
      riemannZeta (1 - s) =
          2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s *
            Complex.cos ((Real.pi : ℂ) * s / 2) * riemannZeta s :=
        riemannZeta_one_sub (hnotneg s hs0) (hnotone s hs1)
      _ = 0 := by simp [b, hunit, hzero]
  let f : ZetaZerosInTraceStrip α → ZetaZerosInTraceStrip α := fun ρ =>
    ⟨1 - (ρ : ℂ), by
      have hz : riemannZeta (1 - (ρ : ℂ)) = 0 :=
        hreflect (ρ : ℂ) ρ.property.2.1 ρ.property.2.2.1 ρ.property.1
      have hre : (1 - (ρ : ℂ)).re = 1 - ρ.val.re := by simp
      have hpos : 0 < (1 - (ρ : ℂ)).re := by
        rw [hre]
        linarith [ρ.property.2.2.1]
      have hlt : (1 - (ρ : ℂ)).re < 1 := by
        rw [hre]
        linarith [ρ.property.2.1]
      have habs : |(1 - (ρ : ℂ)).re - 1 / 2| = |ρ.val.re - 1 / 2| := by
        rw [hre]
        rw [show (1 - ρ.val.re - 1 / 2 : ℝ) = -(ρ.val.re - 1 / 2) by ring]
        rw [abs_neg]
      exact ⟨hz, hpos, hlt, by rw [habs]; exact ρ.property.2.2.2⟩⟩
  let e : ZetaZerosInTraceStrip α ≃ ZetaZerosInTraceStrip α :=
    { toFun := f
      invFun := f
      left_inv := by
        intro ρ
        apply Subtype.ext
        dsimp [f]
        apply Complex.ext <;> norm_num
      right_inv := by
        intro ρ
        apply Subtype.ext
        dsimp [f]
        apply Complex.ext <;> norm_num }
  refine ⟨e, ?_⟩
  intro ρ
  rfl
