-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.kernelResolventReal_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T14:53:34.470401+00:00
-- url     : https://prove2.me/submissions/2d5b2e5f-395b-4bbc-9c39-080d05033482

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
import Theorems.Thm_MarkovProcess_IsSubMarkovKernel_isFiniteKernel
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_integrableOn_kernelResolventReal_integrand

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory ProbabilityTheory Set MarkovProcess
open scoped ENNReal NNReal
open MarkovProcess.SubMarkovKernelSemigroup
variable {alpha : Type*} [MeasurableSpace alpha]

theorem solution (P : SubMarkovKernelSemigroup alpha)
    {lam : ℝ} (hlam : 0 < lam) {f g : alpha → ℝ}
    (hf : Measurable f) (hg : Measurable g) {D E : ℝ}
    (hfD : ∀ y, |f y| ≤ D) (hgE : ∀ y, |g y| ≤ E) :
    P.kernelResolventReal lam (f + g) =
      P.kernelResolventReal lam f + P.kernelResolventReal lam g := by
  funext x
  unfold kernelResolventReal
  change (∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) *
      kernelIntegral (P (Real.toNNReal t)) (f + g) x) =
    (∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) *
      kernelIntegral (P (Real.toNNReal t)) f x) +
    ∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) *
      kernelIntegral (P (Real.toNNReal t)) g x
  rw [← integral_add
    (integrableOn_kernelResolventReal_integrand P hlam hf hfD x)
    (integrableOn_kernelResolventReal_integrand P hlam hg hgE x)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _ht
  let : IsFiniteKernel (P (Real.toNNReal t)) :=
    (P.isSubMarkovKernel (Real.toNNReal t)).isFiniteKernel
  have hfint : Integrable f (P (Real.toNNReal t) x) :=
    Integrable.of_bound hf.stronglyMeasurable.aestronglyMeasurable D
      (Eventually.of_forall hfD)
  have hgint : Integrable g (P (Real.toNNReal t) x) :=
    Integrable.of_bound hg.stronglyMeasurable.aestronglyMeasurable E
      (Eventually.of_forall hgE)
  have hinner : kernelIntegral (P (Real.toNNReal t)) (f + g) x =
      kernelIntegral (P (Real.toNNReal t)) f x +
        kernelIntegral (P (Real.toNNReal t)) g x := by
    unfold kernelIntegral
    simpa only [Pi.add_apply] using integral_add hfint hgint
  dsimp only
  rw [hinner]
  ring
