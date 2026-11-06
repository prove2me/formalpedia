-- Prove2me | solution 1 for OAI.SevenEighths.HeckeTheta.regularizedLatticeL_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:40:20.499987+00:00
-- url     : https://prove2.me/submissions/6f2fb706-c85f-4e33-9d1e-4302c0a3bbd1

import Definitions.Def_OAI_NumberTheory_DirichletL_EisensteinTheta
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Theta
import Theorems.Thm_OAI_SevenEighths_HeckeTheta_regularizedCompleted_eq

set_option autoImplicit false
open OAI
noncomputable section
open Filter Asymptotics Set MeasureTheory
open scoped Topology BigOperators
open OAI.SevenEighths OAI.SevenEighths.HeckeTheta
open EisensteinTheta
namespace OAI.SevenEighths.HeckeTheta
theorem _root_.solution {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    regularizedLatticeL w s = (s - 1) * latticeL w s := by
  unfold regularizedLatticeL latticeL
  rw [regularizedCompleted_eq w hs₀ hs₁]
  ring
end OAI.SevenEighths.HeckeTheta
