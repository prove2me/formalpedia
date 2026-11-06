-- Prove2me | solution 2 for OAI.SevenEighths.HeckeTheta.completed_differentiableAt
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:48:55.05314+00:00
-- url     : https://prove2.me/submissions/bd78ce03-29b7-416c-ac5f-21f8767623f8

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

theorem solution {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) : DifferentiableAt ℂ (completed w) s :=
  WeakFEPair.differentiableAt_Λ (P := pair w) (Or.inl hs₀) (Or.inl hs₁)
