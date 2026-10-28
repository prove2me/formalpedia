-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.existsUnique_continuousProcess_of_hasKolmogorovMoments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T21:36:21.005978+00:00
-- url     : https://prove2.me/submissions/e0fb080b-11a2-43af-9416-b6fc57f1ce19

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_MainSupport
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory MarkovProcess MarkovProcess.SubMarkovKernelSemigroup
open scoped NNReal

theorem solution
    {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
    [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
    [Nonempty alpha] [LocallyCompactSpace alpha]
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (hFeller : P.IsFellerKernelSemigroup) {p q : ℝ} {M : ℝ≥0}
    (hmom : P.HasKolmogorovMoments p q M) :
    ∃! Q : Kernel alpha (ContinuousPath alpha), IsMarkovKernel Q ∧
      ∀ I : Finset NNReal,
        Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I := by
  exact hFeller.existsUnique_continuousProcess P hP
    (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom)
