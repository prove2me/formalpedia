-- Prove2me | solution 1 for OAI.SevenEighths.HeckeTheta.regularizedLatticeL_differentiableAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:40:09.291005+00:00
-- url     : https://prove2.me/submissions/1c22ae07-8f4c-456f-bda1-36f4741c2d16

import Definitions.Def_OAI_NumberTheory_DirichletL_EisensteinTheta
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Theta
import Theorems.Thm_OAI_SevenEighths_HeckeTheta_regularizedCompleted_differentiableAt

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
    DifferentiableAt ℂ (regularizedLatticeL w) s := by
  exact (((differentiable_id.const_cpow (Or.inl
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).differentiableAt).mul
      (Complex.differentiable_one_div_Gamma s)).mul
        (regularizedCompleted_differentiableAt w hs₀)
end OAI.SevenEighths.HeckeTheta
