-- Prove2me | solution 1 for Kyprianou.Ch04.integrableExhaustionTailIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:36:52.072279+00:00
-- url     : https://prove2.me/submissions/af10bdd2-6703-4582-b5f8-6a8e070b3330

import Mathlib
open MeasureTheory Filter
open scoped Topology
set_option autoImplicit false

/-- Integrals of integrable kernels on the complement of increasing covering sets tend to zero. -/
theorem solution {A : Type} [MeasurableSpace A] (mu : Measure A)
    (B : ℕ → Set A) (hB : ∀ n, MeasurableSet (B n))
    (hmono : Monotone B) (hcover : (⋃ n, B n) = Set.univ)
    (g : A → ℝ) (hg : Integrable g mu) :
    Tendsto (fun n => ∫ a, (B n)ᶜ.indicator g a ∂mu) atTop (𝓝 0) := by
  classical
  have h := tendsto_integral_of_dominated_convergence (fun a => ‖g a‖)
    (f := fun _ => (0 : ℝ))
    (fun n => (hg.indicator (hB n).compl).aestronglyMeasurable) hg.norm
    (fun n => Eventually.of_forall fun a => by
      by_cases ha : a ∈ B n <;> simp [Set.indicator_apply, ha])
    (Eventually.of_forall fun a => by
      have ha : a ∈ ⋃ n, B n := by rw [hcover]; exact Set.mem_univ _
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ha
      exact tendsto_atTop_of_eventually_const (i₀ := i) fun n hn => by
        simp [Set.indicator_apply, hmono hn hi])
  simpa only [integral_zero] using h
