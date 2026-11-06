-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.weighted_cauchy_fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:18:44.529976+00:00
-- url     : https://prove2.me/submissions/b62b6d78-abc7-4ae9-abab-ad2fb4c7ea56

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Fibers
import Theorems.Thm_OAI_SevenEighths_InverseMoment_weighted_cauchy
import Theorems.Thm_OAI_SevenEighths_InverseMoment_weightedEnergy_fiber_bound

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open scoped BigOperators
noncomputable section
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (p : ι → κ) (w : ι → ℝ)
    (D : κ → ℝ) (f g : κ → ℂ) (hp : ∀ i ∈ s, p i ∈ t)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hD : ∀ j ∈ t, ∑ i ∈ s with p i = j, w i ≤ D j) :
    ‖∑ i ∈ s, (w i : ℂ) * f (p i) * star (g (p i))‖ ≤
      Real.sqrt (weightedEnergy t D f) * Real.sqrt (weightedEnergy t D g) := by
  apply (weighted_cauchy s w (f ∘ p) (g ∘ p) hw).trans
  exact mul_le_mul
    (Real.sqrt_le_sqrt (weightedEnergy_fiber_bound s t p w D f hp hD))
    (Real.sqrt_le_sqrt (weightedEnergy_fiber_bound s t p w D g hp hD))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
end OAI.SevenEighths.InverseMoment
