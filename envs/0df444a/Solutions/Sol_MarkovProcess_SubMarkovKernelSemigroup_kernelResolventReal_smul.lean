-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.kernelResolventReal_smul
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T14:52:27.894244+00:00
-- url     : https://prove2.me/submissions/ad59983e-8ace-4426-b85e-766530ecc22b

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay
import Definitions.Def_MarkovProcess_SubMarkovKernelSemigroup
import Definitions.Def_MarkovProcess_KernelIntegral
import Definitions.Def_MarkovProcess_KernelResolvents

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory ProbabilityTheory Set MarkovProcess
open scoped ENNReal NNReal
open MarkovProcess.SubMarkovKernelSemigroup
variable {alpha : Type*} [MeasurableSpace alpha]

theorem solution (P : SubMarkovKernelSemigroup alpha)
    (lam a : ℝ) (f : alpha → ℝ) :
    P.kernelResolventReal lam (a • f) = a • P.kernelResolventReal lam f := by
  funext x
  unfold kernelResolventReal
  change (∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) *
      kernelIntegral (P (Real.toNNReal t)) (a • f) x) =
    a * ∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) *
      kernelIntegral (P (Real.toNNReal t)) f x
  rw [← MeasureTheory.integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _ht
  have hinner : kernelIntegral (P (Real.toNNReal t)) (a • f) x =
      a * kernelIntegral (P (Real.toNNReal t)) f x := by
    unfold kernelIntegral
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [MeasureTheory.integral_const_mul]
  dsimp only
  rw [hinner]
  ring
