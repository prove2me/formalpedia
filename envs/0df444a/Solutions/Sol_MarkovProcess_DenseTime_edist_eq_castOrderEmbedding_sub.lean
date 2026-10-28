-- Prove2me | solution 1 for MarkovProcess.DenseTime.edist_eq_castOrderEmbedding_sub
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T14:03:41.894232+00:00
-- url     : https://prove2.me/submissions/cb61df4d-85a0-49a6-92f2-439d945fc52c

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
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MarkovProcess
open MarkovProcess.DenseTime
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



theorem solution {s t : DenseTime} (hst : s ≤ t) :
    edist s t = ((castOrderEmbedding t - castOrderEmbedding s : ℝ≥0) : ℝ≥0∞) := by
  have hcast : castOrderEmbedding s ≤ castOrderEmbedding t :=
    castOrderEmbedding.monotone hst
  have hcoe : ∀ r : DenseTime, ((castOrderEmbedding r : ℝ≥0) : ℝ) = ((r : ℚ) : ℝ) := by
    intro r
    simp only [castOrderEmbedding, NNRat.castOrderEmbedding_apply]
    push_cast
    rfl
  have hreal : ((s : ℚ) : ℝ) ≤ ((t : ℚ) : ℝ) := by
    rw [← hcoe s, ← hcoe t]
    exact_mod_cast hcast
  rw [edist_dist, ← ENNReal.ofReal_coe_nnreal]
  congr 1
  rw [NNReal.coe_sub hcast, NNRat.dist_eq, ← Rat.dist_cast, Real.dist_eq, hcoe, hcoe,
    abs_sub_comm, abs_of_nonneg (by linarith only [hreal])]
