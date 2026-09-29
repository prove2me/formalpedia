-- Prove2me | solution 1 for InvariantMean.not_exists_translationInvariant_normalised_functional_int
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-22T10:08:52.156452+00:00
-- url     : https://prove2.me/submissions/64aa2230-4439-4af3-86d3-a29684839ba3

import Mathlib

/-!
No translation-invariant normalised linear functional exists on all of `ℤ → ℝ`.

The witness is the unbounded `n ↦ n`, whose translate by one differs from it by the constant
function `1`. Invariance equates the two values, linearity turns the difference into the value
at the constant function, and normalisation then contradicts itself. Positivity is never used,
so this is stronger than the failure of an invariant *mean*: not even a bare linear functional
survives once the domain is widened from the bounded functions to all of them.
-/

theorem solution :
    ¬ ∃ m : (ℤ → ℝ) →ₗ[ℝ] ℝ,
      (∀ f : ℤ → ℝ, m (fun n => f (n - 1)) = m f) ∧ m (fun _ => (1 : ℝ)) = 1 := by
  rintro ⟨m, hinv, hone⟩
  have key : (fun n : ℤ => ((n - 1 : ℤ) : ℝ))
      = (fun n : ℤ => (n : ℝ)) - (fun _ : ℤ => (1 : ℝ)) := by
    funext n
    simp only [Pi.sub_apply]
    push_cast
    ring
  have h := hinv (fun n : ℤ => (n : ℝ))
  rw [key, map_sub, hone] at h
  linarith [h]
