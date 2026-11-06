-- Prove2me | solution 1 for OAI.SevenEighths.HeckeTheta.completed_differentiableAt_of_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:40:50.826459+00:00
-- url     : https://prove2.me/submissions/a089fe48-d458-4b3f-86e7-c66fba533af4

import Definitions.Def_OAI_NumberTheory_DirichletL_EisensteinTheta
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Theta
import Theorems.Thm_P2M_OAI_SevenEighths_HeckeTheta_pair_g__eq_zero_5068f1b5229c

set_option autoImplicit false
open OAI
noncomputable section
open Filter Asymptotics Set MeasureTheory
open scoped Topology BigOperators
open OAI.SevenEighths OAI.SevenEighths.HeckeTheta
open EisensteinTheta
namespace OAI.SevenEighths.HeckeTheta
theorem _root_.solution {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) (hw : ∑ a, w a = 0) {s : ℂ} (hs₀ : s ≠ 0) :
    DifferentiableAt ℂ (completed w) s :=
  (pair w).differentiableAt_Λ (Or.inl hs₀) (Or.inr (pair_g₀_eq_zero w hw))
end OAI.SevenEighths.HeckeTheta
