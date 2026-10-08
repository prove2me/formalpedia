-- Prove2me | solution 1 for MondererShapley.Congestion.sub_potential_indep
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T01:15:33.608624+00:00
-- url     : https://prove2.me/submissions/b6aa6c26-fb73-47e0-93ea-a2a6abedf189

import Mathlib
import Definitions.Def_MondererShapley_ClosedPath_IsPotential

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : ι → Type*}
    (u : ι → (∀ i, Y i) → ℝ) (P : (∀ i, Y i) → ℝ) (hP : MondererShapley.ClosedPath.IsPotential u P)
    (i : ι) (a : ∀ k, Y k) (x z : Y i) :
    u i (Function.update a i x) - P (Function.update a i x) =
      u i (Function.update a i z) - P (Function.update a i z) := by
  have h := hP i a x z
  linarith

#print axioms solution
