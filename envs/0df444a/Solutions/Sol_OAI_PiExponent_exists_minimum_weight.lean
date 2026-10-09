-- Prove2me | solution 1 for OAI.PiExponent.exists_minimum_weight
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T10:14:16.47199+00:00
-- url     : https://prove2.me/submissions/d776678c-ec1b-4e66-8399-b4f537e21527

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic



theorem solution
    (m : ℕ) (hm : 1 ≤ m) (w : Fin m → ℝ) (X : ℝ)
    (hX : ∀ i, X < w i) :
    ∃ wstar : ℝ, X < wstar ∧ (∀ i, wstar ≤ w i) ∧
      ∃ i, wstar = w i := by
  have hne : (Finset.univ : Finset (Fin m)).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ w hne
  exact ⟨w i, hX i, (fun j => hi j (Finset.mem_univ j)), i, rfl⟩

#print axioms solution
