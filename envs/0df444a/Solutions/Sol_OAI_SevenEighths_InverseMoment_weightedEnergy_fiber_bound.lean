-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.weightedEnergy_fiber_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:00:51.286119+00:00
-- url     : https://prove2.me/submissions/f112db42-4e2f-4df7-9b7e-22c6d8d7619d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Fibers
import Theorems.Thm_OAI_SevenEighths_InverseMoment_fiber_energy_bound

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open scoped BigOperators
noncomputable section
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (p : ι → κ) (w : ι → ℝ)
    (D : κ → ℝ) (f : κ → ℂ) (hp : ∀ i ∈ s, p i ∈ t)
    (hD : ∀ j ∈ t, ∑ i ∈ s with p i = j, w i ≤ D j) :
    weightedEnergy s w (f ∘ p) ≤ weightedEnergy t D f := by
  exact fiber_energy_bound s t p w D (fun j => ‖f j‖ ^ 2) hp
    (fun j _ => sq_nonneg _) hD
end OAI.SevenEighths.InverseMoment
