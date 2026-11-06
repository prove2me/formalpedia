-- Prove2me | solution 1 for OAI.SevenEighths.HeckeTheta.completed_functional_equation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:10:16.752192+00:00
-- url     : https://prove2.me/submissions/b4a38523-18fe-4e60-b196-9cd099b8c16e

import Definitions.Def_OAI_NumberTheory_DirichletL_EisensteinTheta
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Theta
import Theorems.Thm_OAI_SevenEighths_HeckeTheta_pair_k
import Theorems.Thm_OAI_SevenEighths_EisensteinTheta_parityPair_k
import Theorems.Thm_OAI_SevenEighths_ThetaProduct_rectangularPair_k
attribute [local simp] OAI.SevenEighths.EisensteinTheta.parityPair_k
attribute [local simp] OAI.SevenEighths.ThetaProduct.rectangularPair_k


attribute [local simp] OAI.SevenEighths.HeckeTheta.pair_k

set_option autoImplicit false
open OAI
noncomputable section
open Filter Asymptotics Set MeasureTheory
open scoped Topology BigOperators
open OAI.SevenEighths OAI.SevenEighths.HeckeTheta
open EisensteinTheta
namespace OAI.SevenEighths.HeckeTheta
theorem _root_.solution {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) (s : ℂ) :
    completed w (1 - s) = (pair w).symm.Λ s := by
  change (pair w).Λ (1 - s) = (pair w).symm.Λ s
  simpa only [pair_k, Complex.ofReal_one, show (pair w).ε = 1 from rfl, one_smul] using
    (pair w).functional_equation s
end OAI.SevenEighths.HeckeTheta
