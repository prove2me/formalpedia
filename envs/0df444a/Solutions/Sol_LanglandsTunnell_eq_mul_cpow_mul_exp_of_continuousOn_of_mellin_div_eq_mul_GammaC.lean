-- Prove2me | solution 1 for LanglandsTunnell.eq_mul_cpow_mul_exp_of_continuousOn_of_mellin_div_eq_mul_GammaC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/75d1c910-b3f8-5223-aaa2-3e7f9308d4bf

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_eq_mul_cpow_mul_exp_of_continuousOn_of_mellin_div_eq_mul_GammaC

set_option autoImplicit false

open Complex

theorem solution
    (Wr : ℝ → ℂ) (A ν : ℂ) (σ₀ : ℝ)
    (hcont : ContinuousOn Wr (Set.Ioi 0))
    (hM : ∀ s : ℂ, σ₀ < s.re →
      MellinConvergent (fun t : ℝ => Wr t / (t : ℂ)) s ∧
        mellin (fun t : ℝ => Wr t / (t : ℂ)) s = A * Complex.Gammaℂ (s + ν)) :
    ∀ t : ℝ, 0 < t →
      Wr t = 2 * A * ((t : ℂ) ^ (ν + 1)) * Complex.exp (-(2 * Real.pi * t : ℝ)) := by

  obtain ⟨E, hE⟩ : ∃ E : ℝ → ℂ, E = fun u : ℝ => ((Real.exp (-u) : ℝ) : ℂ) := ⟨_, rfl⟩
  have hEconv : ∀ z : ℂ, 0 < z.re → MellinConvergent E z := by
    intro z hz
    have h := Complex.GammaIntegral_convergent hz
    refine (h.congr_fun (fun x _ => ?_) measurableSet_Ioi)
    simp only [hE, smul_eq_mul, mul_comm]
  have hEmel : ∀ z : ℂ, 0 < z.re → mellin E z = Complex.Gamma z := by
    intro z hz
    rw [Complex.Gamma_eq_integral hz, Complex.GammaIntegral_eq_mellin, hE]

  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℂ, g = fun t : ℝ => 2 * A * ((t : ℂ) ^ ν) * Complex.exp (-(2 * Real.pi * t : ℝ)) :=
    ⟨_, rfl⟩
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have hgE : g = fun t : ℝ => (2 * A) • ((t : ℂ) ^ ν • E (2 * Real.pi * t)) := by
    funext t
    simp only [hg, hE, smul_eq_mul, Complex.ofReal_exp, Complex.ofReal_neg]
    ring
  have hGconv : ∀ s : ℂ, -ν.re < s.re → MellinConvergent g s := by
    intro s hs
    rw [hgE]
    refine MellinConvergent.const_smul ?_ (2 * A)
    rw [MellinConvergent.cpow_smul, MellinConvergent.comp_mul_left h2π]
    exact hEconv _ (by simp; linarith)
  have hGmel : ∀ s : ℂ, -ν.re < s.re → mellin g s = A * Complex.Gammaℂ (s + ν) := by
    intro s hs
    rw [hgE, mellin_const_smul, mellin_cpow_smul, mellin_comp_mul_left _ _ h2π, hEmel _ (by simp; linarith),
      Complex.Gammaℂ_def, smul_eq_mul, smul_eq_mul]
    push_cast
    ring

  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℂ, f = fun t : ℝ => Wr t / (t : ℂ) := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : ℝ → ℂ, h = fun t : ℝ => f t - g t := ⟨_, rfl⟩
  have hHconv : ∀ s : ℂ, σ₀ < s.re → -ν.re < s.re → MellinConvergent h s ∧ mellin h s = 0 := by
    intro s hs1 hs2
    obtain ⟨hf1, hf2⟩ := hM s hs1
    rw [← hf] at hf1 hf2
    have hg1 := hGconv s hs2
    have hg2 := hGmel s hs2
    have hint : MellinConvergent h s := by
      have := (MeasureTheory.Integrable.sub hf1 hg1)
      refine this.congr ?_
      filter_upwards with t
      simp only [hh, smul_sub, Pi.sub_apply]
    refine ⟨hint, ?_⟩
    have : mellin h s = mellin f s - mellin g s := by
      unfold mellin
      rw [← MeasureTheory.integral_sub hf1 hg1]
      congr 1
      funext t
      simp only [hh, smul_sub]
    rw [this, hf2, hg2, sub_self]

  obtain ⟨σ, hσ₀, hσν⟩ : ∃ σ : ℝ, σ₀ < σ ∧ -ν.re < σ :=
    ⟨max σ₀ (-ν.re) + 1, by have := le_max_left σ₀ (-ν.re); linarith,
      by have := le_max_right σ₀ (-ν.re); linarith⟩
  have hre : ∀ y : ℝ, ((σ : ℂ) + (y : ℂ) * I).re = σ := by intro y; simp
  have hline : ∀ y : ℝ, mellin h ((σ : ℂ) + (y : ℂ) * I) = 0 := fun y =>
    (hHconv _ (by rw [hre]; exact hσ₀) (by rw [hre]; exact hσν)).2
  have hconvσ : MellinConvergent h (σ : ℂ) :=
    (hHconv _ (by rw [Complex.ofReal_re]; exact hσ₀) (by rw [Complex.ofReal_re]; exact hσν)).1
  intro t ht
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hcontf : ContinuousAt f t := by
    rw [hf]
    have h1 : ContinuousAt Wr t := hcont.continuousAt (Ioi_mem_nhds ht)
    have h2 : ContinuousAt (fun u : ℝ => (u : ℂ)) t := Complex.continuous_ofReal.continuousAt
    exact ContinuousAt.div (f := Wr) (g := fun u : ℝ => (u : ℂ)) h1 h2 ht0
  have hcontg : ContinuousAt g t := by
    rw [hg]
    have h1 : ContinuousAt (fun u : ℝ => (u : ℂ) ^ ν) t :=
      Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr ht.ne')
    have h2 : Continuous (fun u : ℝ => Complex.exp (-((2 * Real.pi * u : ℝ) : ℂ))) := by
      apply Complex.continuous_exp.comp
      apply Continuous.neg
      exact Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)
    exact ((continuousAt_const.mul h1).mul h2.continuousAt)
  have hconth : ContinuousAt h t := by
    rw [hh]
    exact hcontf.sub hcontg
  have hvert : VerticalIntegrable (mellin h) σ := by
    unfold VerticalIntegrable
    have hz : (fun y : ℝ => mellin h (↑σ + ↑y * I)) = fun _ => (0 : ℂ) := funext hline
    rw [hz]
    exact MeasureTheory.integrable_zero _ _ _
  have hinv := mellinInv_mellin_eq σ h ht hconvσ hvert hconth
  have hzero : mellinInv σ (mellin h) t = 0 := by
    unfold mellinInv
    have hz : (fun y : ℝ => (t : ℂ) ^ (-(↑σ + ↑y * I)) • mellin h (↑σ + ↑y * I)) = fun _ => 0 := by
      funext y
      rw [hline y, smul_zero]
    rw [hz, MeasureTheory.integral_zero, smul_zero]
  have hft : f t = g t := by
    have : h t = 0 := by rw [← hinv, hzero]
    rw [hh] at this
    exact sub_eq_zero.mp this

  have hW : Wr t = (t : ℂ) * g t := by
    rw [hf] at hft
    have := hft
    rw [← this, mul_div_cancel₀ _ ht0]
  rw [hW, hg, Complex.cpow_add _ _ ht0, Complex.cpow_one]
  ring

#print axioms solution

end S_LanglandsTunnell_eq_mul_cpow_mul_exp_of_continuousOn_of_mellin_div_eq_mul_GammaC
end P2MW
export P2MW.S_LanglandsTunnell_eq_mul_cpow_mul_exp_of_continuousOn_of_mellin_div_eq_mul_GammaC (solution)
