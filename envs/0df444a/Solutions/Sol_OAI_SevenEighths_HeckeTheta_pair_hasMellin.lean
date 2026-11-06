-- Prove2me | solution 1 for OAI.SevenEighths.HeckeTheta.pair_hasMellin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:39:28.977748+00:00
-- url     : https://prove2.me/submissions/a5dd14a6-32d2-4b85-b2d2-93d3a9d3eb1b

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
    {s : ℂ} (hs : 1 < s.re) :
    HasMellin (fun t => (pair w).f t - (pair w).f₀) s (completed w s) :=
  (pair w).hasMellin (by simpa using hs)
end OAI.SevenEighths.HeckeTheta
