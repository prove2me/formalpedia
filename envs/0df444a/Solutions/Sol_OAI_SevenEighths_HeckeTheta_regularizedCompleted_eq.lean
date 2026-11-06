-- Prove2me | solution 1 for OAI.SevenEighths.HeckeTheta.regularizedCompleted_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:39:32.732042+00:00
-- url     : https://prove2.me/submissions/145caf11-4b58-4494-a581-5d7203e3cf9b

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
theorem _root_.solution {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    regularizedCompleted w s = (s - 1) * completed w s := by
  unfold regularizedCompleted completed WeakFEPair.Λ
  simp only [pair_k, Complex.ofReal_one, show (pair w).ε = 1 from rfl,
    smul_eq_mul, one_div]
  have hsub : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr hs₁.symm
  field_simp
  ring
end OAI.SevenEighths.HeckeTheta
