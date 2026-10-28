-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.finiteTimeKernel_two_map_pair
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:10:06.846583+00:00
-- url     : https://prove2.me/submissions/7fba110e-0a51-4673-a7fe-6e37095e31f7

import Definitions.Def_MarkovProcess_DenseTime_ConditionalKernel
import Definitions.Def_MarkovProcess_DenseTime_PrefixKernel
import Definitions.Def_MarkovProcess_DenseTime_PrefixRecursion
import Definitions.Def_MarkovProcess_DenseTime_Trajectory
import Definitions.Def_MarkovProcess_FiniteTime_Kernel
import Definitions.Def_MarkovProcess_FiniteTime_ProjectiveFamily
import Definitions.Def_MarkovProcess_Kernel_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_KernelSemigroup_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_KolmogorovMoments_SourceClosedV3
import Definitions.Def_MarkovProcess_Time_CountableDenseTime
import Definitions.Def_MarkovProcess_Time_DenseTimeHistory
import Definitions.Def_MarkovProcess_Time_FiniteOrderedTimes
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Process.Kolmogorov
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_finiteTimeKernel_one_map_eval
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup MarkovProcess.SubMarkovKernelSemigroup.IsConservative
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Two-point marginals of the dense-time trajectory, and the intrinsic Kolmogorov bridge

The dense-time trajectory of a conservative sub-Markov kernel semigroup already has identified
one-time marginals.  This file identifies its two-time marginals: at dense times whose physical
images satisfy `iota d < iota d'`, the pair `(path d, path d')` has the law obtained by running
`P` for time `iota d` and then, from the state reached, for the increment `iota d' - iota d`.

The identification is then used to discharge the coordinate Kolmogorov hypothesis that every
trajectory theorem of the library assumes.  Under the intrinsic semigroup bound
`SubMarkovKernelSemigroup.HasKolmogorovMoments`, the canonical dense-time coordinate process is a
Kolmogorov process with a positive Hölder exponent below `(q - 1) / p`.

No continuity, modification, Markov-property, or path-regularity statement is proved here; only
the two-point law and the moment estimate it transports.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


noncomputable section











variable {A B C E : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
  [MeasurableSpace E]

/-- A composition-product whose second factor ignores the starting point is the measure-level
composition-product of the first factor's law with that second factor. -/
private theorem compProd_prodMkLeft_apply (kappa : Kernel A B) [IsSFiniteKernel kappa]
    (eta : Kernel B C) [IsSFiniteKernel eta] (x : A) :
    (kappa ⊗ₖ Kernel.prodMkLeft A eta) x = (kappa x) ⊗ₘ eta := by
  ext s hs
  rw [Kernel.compProd_apply hs, Measure.compProd_apply hs]
  simp only [Kernel.prodMkLeft_apply]

/-- Pushing the second coordinate of such a composition-product forward along a measurable map
is the composition-product with the pushed-forward second factor. -/
private theorem compProd_prodMkLeft_map (kappa : Kernel A B) [IsSFiniteKernel kappa]
    (eta : Kernel B C) [IsSFiniteKernel eta] {g : C → E} (hg : Measurable g) :
    (kappa ⊗ₖ Kernel.prodMkLeft A eta).map (Prod.map id g) =
      kappa ⊗ₖ Kernel.prodMkLeft A (eta.map g) := by
  ext x
  rw [Kernel.map_apply _ (measurable_id.prodMap hg), compProd_prodMkLeft_apply,
    compProd_prodMkLeft_apply, Measure.compProd_map hg]



variable {D alpha : Type*} [MeasurableSpace alpha]

private theorem measurable_finConsOne :
    Measurable
      (fun z : alpha × (Fin 1 → alpha) ↦ @Fin.cons 1 (fun _ : Fin 2 ↦ alpha) z.1 z.2) := by
  rw [measurable_pi_iff]
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa only [Fin.cons_zero] using
      (measurable_fst : Measurable (Prod.fst : alpha × (Fin 1 → alpha) → alpha))
  · simpa only [Fin.cons_succ] using!
      (measurable_pi_apply j).comp
        (measurable_snd : Measurable (Prod.snd : alpha × (Fin 1 → alpha) → _))



theorem solution (P : SubMarkovKernelSemigroup alpha)
    (hP : P.IsConservative) (u : FiniteOrderedTimes 2) :
    (finiteTimeKernel P u).map (fun path ↦ (path 0, path 1)) =
      P (u 0) ⊗ₖ Kernel.prodMkLeft alpha (P (u 1 - u 0)) := by
  let : IsFiniteKernel (P (u 0)) := (P.isSubMarkovKernel (u 0)).isFiniteKernel
  let : IsFiniteKernel (P (u.relativeTail 0)) :=
    (P.isSubMarkovKernel (u.relativeTail 0)).isFiniteKernel
  let : IsMarkovKernel (finiteTimeKernel P u.relativeTail) :=
    hP.isMarkovKernel_finiteTimeKernel P u.relativeTail
  have hmeasPair : Measurable (fun path : Fin 2 → alpha ↦ (path 0, path 1)) := by fun_prop
  have hcomp :
      (fun path : Fin 2 → alpha ↦ (path 0, path 1)) ∘
          (fun z : alpha × (Fin 1 → alpha) ↦ @Fin.cons 1 (fun _ : Fin 2 ↦ alpha) z.1 z.2) =
        Prod.map id (fun path : Fin 1 → alpha ↦ path 0) := by
    funext z
    rfl
  have htail : u.relativeTail 0 = u 1 - u 0 := rfl
  rw [finiteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map,
    ← Kernel.map_comp_right _ measurable_finConsOne hmeasPair, hcomp,
    compProd_prodMkLeft_map _ _ (measurable_pi_apply (0 : Fin 1)),
    finiteTimeKernel_one_map_eval, htail]
