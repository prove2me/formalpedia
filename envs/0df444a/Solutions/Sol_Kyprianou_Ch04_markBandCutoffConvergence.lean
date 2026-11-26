-- Prove2me | solution 1 for Kyprianou.Ch04.markBandCutoffConvergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:38:30.576752+00:00
-- url     : https://prove2.me/submissions/f27baafb-baa3-4839-9aaa-4126408bb197

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_lpNormSqIntegral
import Theorems.Thm_Kyprianou_Ch04_integrableExhaustionTailIntegral
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

/-- Finite-band truncations of a measurable L1 and L2 kernel converge in both norms. -/
theorem solution {A : Type} [MeasurableSpace A] (mu : Measure A)
    (B : ℕ → Set A) (hB : ∀ n, MeasurableSet (B n))
    (hmono : Monotone B) (hcover : (⋃ n, B n) = Set.univ)
    (g : A → ℝ) (hgi : Integrable g mu) (hg : MemLp g 2 mu) :
    let f := fun n => (B n).indicator g
    let hf : ∀ n, MemLp (f n) 2 mu := fun n => hg.indicator (hB n)
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) ∧
      Tendsto (fun n => ∫ a, |f n a - g a| ∂mu) atTop (𝓝 0) := by
  classical
  let f := fun n => (B n).indicator g
  let hf : ∀ n, MemLp (f n) 2 mu := fun n => hg.indicator (hB n)
  have habs (n : ℕ) : (fun a => |f n a - g a|) = (B n)ᶜ.indicator (fun a => |g a|) := by
    funext a
    by_cases ha : a ∈ B n <;> simp [f, Set.indicator_apply, ha]
  have hsq (n : ℕ) : (fun a => (f n a - g a)^2) = (B n)ᶜ.indicator (fun a => (g a)^2) := by
    funext a
    by_cases ha : a ∈ B n <;> simp [f, Set.indicator_apply, ha]
  refine ⟨?_,?_⟩
  · have h := Kyprianou.Ch04.integrableExhaustionTailIntegral mu B hB hmono hcover
      (fun a => (g a)^2) hg.integrable_sq
    have he (n : ℕ) : dist ((hf n).toLp (f n)) (hg.toLp g) ^ 2 =
        ∫ a, (B n)ᶜ.indicator (fun a => (g a)^2) a ∂mu := by
      rw [dist_eq_norm, ← MemLp.toLp_sub]
      exact (Kyprianou.Ch04.lpNormSqIntegral mu (f n - g) ((hf n).sub hg)).trans
        (congrArg (fun k : A → ℝ => ∫ a, k a ∂mu) (hsq n))
    have hh : Tendsto (fun n => Real.sqrt (∫ a, (B n)ᶜ.indicator
        (fun a => (g a)^2) a ∂mu)) atTop (𝓝 (Real.sqrt 0)) :=
      Real.continuous_sqrt.continuousAt.tendsto.comp h
    simp only [← he, Real.sqrt_sq dist_nonneg, Real.sqrt_zero] at hh
    exact tendsto_iff_dist_tendsto_zero.mpr hh
  · have h := Kyprianou.Ch04.integrableExhaustionTailIntegral mu B hB hmono hcover
      (fun a => |g a|) (by simpa only [Real.norm_eq_abs] using hgi.norm)
    change Tendsto (fun n => ∫ a, |f n a - g a| ∂mu) atTop (𝓝 0)
    simp_rw [habs]
    exact h
