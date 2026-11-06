-- Prove2me | solution 1 for OAI.SevenEighths.HeckeTheta.regularizedCompleted_differentiableAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:39:30.960512+00:00
-- url     : https://prove2.me/submissions/87301b0b-af41-4985-b82b-1d2ee7d10a76

import Definitions.Def_OAI_NumberTheory_DirichletL_EisensteinTheta
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Theta

set_option autoImplicit false
open OAI
noncomputable section
open Filter Asymptotics Set MeasureTheory
open scoped Topology BigOperators
open OAI.SevenEighths OAI.SevenEighths.HeckeTheta
open EisensteinTheta
namespace OAI.SevenEighths.HeckeTheta
theorem _root_.solution {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) {s : ℂ} (hs₀ : s ≠ 0) :
    DifferentiableAt ℂ (regularizedCompleted w) s := by
  exact (((differentiableAt_id.sub_const 1).mul
    (((pair w).differentiable_Λ₀ s).sub
      ((differentiableAt_id.inv hs₀).mul_const (pair w).f₀))).add_const (pair w).g₀)
end OAI.SevenEighths.HeckeTheta
