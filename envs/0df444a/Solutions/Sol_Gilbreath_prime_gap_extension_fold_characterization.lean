-- Prove2me | solution 1 for Gilbreath.prime_gap_extension_fold_characterization
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T03:51:32.583797+00:00
-- url     : https://prove2.me/submissions/e583e1a2-c10c-4303-b81a-2f1ad89dd16a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_gilbreath_finite_extension
import Theorems.Thm_Gilbreath_prime_gap_ordered_extension_condition

namespace Gilbreath

/-- The fold never drops below `x - sum`. -/
theorem sol_fold_add_sum_ge : ∀ (es : List ℕ) (x : ℕ), x ≤ extensionFold es x + es.sum
  | [], x => by simp [extensionFold]
  | e :: es, x => by
    have ih := sol_fold_add_sum_ge es (Int.natAbs ((x : ℤ) - (e : ℤ)))
    simp only [extensionFold, List.sum_cons]
    omega

/-- Interval completeness makes every `x ≤ sum + 1` fold into `{0,1}`. -/
theorem sol_fold_le_one_of_complete : ∀ (es : List ℕ), ExtensionComplete es →
    ∀ x : ℕ, x ≤ es.sum + 1 → extensionFold es x ≤ 1
  | [], _, x, hx => by simpa [extensionFold] using hx
  | e :: es, hc, x, hx => by
    obtain ⟨he, hc⟩ := hc
    simp only [extensionFold]
    apply sol_fold_le_one_of_complete es hc
    simp only [List.sum_cons] at hx
    omega

end Gilbreath

open Gilbreath in
theorem solution (b : ℕ → ℕ)
    (hb : ∀ n, d 1 (n + 1) = 2 * b n) (n : ℕ)
    (hprefix : ∀ j, j < n → iterAbsDiff b j 0 ≤ 1) :
    ∀ x : ℕ, extensionFold (extensionBoundary b n) x ≤ 1 ↔
      x ≤ (extensionBoundary b n).sum + 1 := by
  intro x
  constructor
  · intro h
    have := sol_fold_add_sum_ge (extensionBoundary b n) x
    omega
  · exact sol_fold_le_one_of_complete _ (prime_gap_ordered_extension_condition b hb n hprefix) x
