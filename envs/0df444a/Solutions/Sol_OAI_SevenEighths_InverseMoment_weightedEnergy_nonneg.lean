-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.weightedEnergy_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:18:43.505496+00:00
-- url     : https://prove2.me/submissions/c4196e26-bb27-4230-8b4b-c61ecc481068

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Fibers

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open scoped BigOperators
noncomputable section
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (f : ι → ℂ) (hw : ∀ i ∈ s, 0 ≤ w i) : 0 ≤ weightedEnergy s w f := by
  exact Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)
end OAI.SevenEighths.InverseMoment
