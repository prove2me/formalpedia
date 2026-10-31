-- Prove2me | solution 1 for MarkovProcess.hasContinuousC0Orbits_driftSemigroup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:43:29.293561+00:00
-- url     : https://prove2.me/submissions/a2228fca-a977-42e0-a5d2-121a88b5f0d8

import Definitions.Def_MarkovProcess_V3H_Examples_Drift_f1e2d4e2
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompNotation
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The deterministic drift semigroup and its continuous-path process

On a finite-dimensional real normed space the transition semigroup that translates by `t • v` in
time `t` is a conservative Feller semigroup satisfying the Kolmogorov moment criterion with
exponents `p = q = 2` and constant `‖v‖²`.  The existence-and-uniqueness theorem of
`MarkovProcess.Main` therefore applies, and the process it produces is identified: from every
starting point `x` its law is the Dirac mass at the straight line `t ↦ x + t • v`.

Together with `MarkovProcess.Examples.Identity` this shows that the hypotheses of the main
theorem are satisfiable by a semigroup that genuinely moves.  Nothing here is claimed about a
semigroup with a nonzero diffusion part; for that see `MarkovProcess.Examples.HeatSemigroup`.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

section Definition









end Definition

section Feller











end Feller

section Moments



end Moments

section Process













end Process

end

end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The deterministic drift semigroup and its continuous-path process

On a finite-dimensional real normed space the transition semigroup that translates by `t • v` in
time `t` is a conservative Feller semigroup satisfying the Kolmogorov moment criterion with
exponents `p = q = 2` and constant `‖v‖²`.  The existence-and-uniqueness theorem of
`MarkovProcess.Main` therefore applies, and the process it produces is identified: from every
starting point `x` its law is the Dirac mass at the straight line `t ↦ x + t • v`.

Together with `MarkovProcess.Examples.Identity` this shows that the hypotheses of the main
theorem are satisfiable by a semigroup that genuinely moves.  Nothing here is claimed about a
semigroup with a nonzero diffusion part; for that see `MarkovProcess.Examples.HeatSemigroup`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ZeroAtInfty



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]









namespace MarkovProcess

end MarkovProcess
open MarkovProcess
theorem solution (v : E) :
    (driftSemigroup v).HasContinuousC0Orbits (mapsC0_driftSemigroup v) := by
  intro f
  rw [Metric.continuous_iff]
  intro b eps heps
  obtain ⟨delta, hdelta, hf⟩ := Metric.uniformContinuous_iff.mp
    (ZeroAtInftyContinuousMap.uniformContinuous f) (eps / 2) (half_pos heps)
  have hv : (0 : ℝ) < ‖v‖ + 1 := by positivity
  refine ⟨delta / (‖v‖ + 1), div_pos hdelta hv, fun a hab ↦ ?_⟩
  have hab' : |(a : ℝ) - (b : ℝ)| < delta / (‖v‖ + 1) := by
    rw [← NNReal.dist_eq]
    exact hab
  have hkey : ∀ x : E, dist (f (x + (a : ℝ) • v)) (f (x + (b : ℝ) • v)) ≤ eps / 2 := by
    intro x
    refine le_of_lt (hf ?_)
    have hsub : (x + (a : ℝ) • v) - (x + (b : ℝ) • v) = ((a : ℝ) - (b : ℝ)) • v := by
      rw [sub_smul]
      abel
    rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs]
    calc |(a : ℝ) - (b : ℝ)| * ‖v‖ ≤ |(a : ℝ) - (b : ℝ)| * (‖v‖ + 1) :=
          mul_le_mul_of_nonneg_left (by linarith only []) (abs_nonneg _)
      _ < delta / (‖v‖ + 1) * (‖v‖ + 1) := mul_lt_mul_of_pos_right hab' hv
      _ = delta := div_mul_cancel₀ delta (ne_of_gt hv)
  have hle : dist ((driftSemigroup v).c0Operator (mapsC0_driftSemigroup v) a f)
      ((driftSemigroup v).c0Operator (mapsC0_driftSemigroup v) b f) ≤ eps / 2 := by
    rw [← ZeroAtInftyContinuousMap.dist_toBCF_eq_dist]
    refine (BoundedContinuousFunction.dist_le (le_of_lt (half_pos heps))).2 fun x ↦ ?_
    show dist ((driftSemigroup v).c0Operator (mapsC0_driftSemigroup v) a f x)
      ((driftSemigroup v).c0Operator (mapsC0_driftSemigroup v) b f x) ≤ eps / 2
    rw [SubMarkovKernelSemigroup.c0Operator_apply, SubMarkovKernelSemigroup.c0Operator_apply,
      kernelIntegral_driftSemigroup_apply, kernelIntegral_driftSemigroup_apply]
    exact hkey x
  linarith only [hle, heps]
