-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.finiteTimeKernel_cemeterySemigroup_delta
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:42:13.827996+00:00
-- url     : https://prove2.me/submissions/8f9041c6-ed17-44bf-8fe0-78711cef528b

import Definitions.Def_MarkovProcess_V3H_DenseTime_CemeterySemigroup_149c26e5
import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelEquivariance_10113825
import Definitions.Def_MarkovProcess_V3H_Killed_Process_a15f3c27
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
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
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
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Conservative cemetery extension of a sub-Markov kernel

This file adjoins an isolated cemetery state to a measurable state space and
extends one sub-Markov kernel to a Markov kernel.  It deliberately makes no
claim about preservation of kernel composition or semigroup laws.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

namespace MarkovProcess

variable {α : Type*}









namespace Kernel

variable [MeasurableSpace α]





















/-- The cemetery state is absorbing under the conservative extension. -/
theorem cemeteryExtension_absorbing (κ : ProbabilityTheory.Kernel α α) :
    cemeteryExtension κ Cemetery.delta = Measure.dirac Cemetery.delta :=
  cemeteryExtension_delta_apply κ

end Kernel

end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Cemetery extensions of sub-Markov kernel semigroups

This file shows that conservative cemetery extension preserves the identity
kernel and composition of sub-Markov kernels.  Consequently, applying the
extension at every time turns any sub-Markov kernel semigroup into a
conservative semigroup on the cemetery state space.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace MarkovProcess

variable {α : Type*} [MeasurableSpace α]

namespace Kernel







end Kernel

namespace SubMarkovKernelSemigroup



variable (P : SubMarkovKernelSemigroup α)





/-- The cemetery state is absorbing at every time in the extension semigroup. -/
theorem cemeterySemigroup_absorbing (t : NNReal) :
    cemeterySemigroup P t Cemetery.delta = Measure.dirac Cemetery.delta :=
  by rw [cemeterySemigroup_apply]; exact Kernel.cemeteryExtension_absorbing (P t)

end SubMarkovKernelSemigroup

end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite-dimensional distributions of the killed process

For the continuous-path process of a conservative Feller semigroup and an open set `U`, this file
identifies every finite-dimensional distribution of the process killed at the exit of `U`
(`killedProcess P hP U hU` of `Killed/Process.lean`, a law on lifetime paths in the carrier `U`)
with the corresponding finite-dimensional distribution of the **cemetery extension of the killed
semigroup** on `U`:

  `(killedProcess x).map (fun ω ↦ fun i : I ↦ coordinate i ω) =
      finiteSetKernel (cemeterySemigroup (killedSemigroup P hP U hU hFeller hK)) I (alive x)`

(`killedProcess_map_finiteEvaluation`), and, at a strictly increasing family of times, the
corresponding statement for `finiteTimeKernel` (`killedProcess_map_coordinates_ordered`).

The proof is by induction on the number of times, along the recursion of `finiteTimeKernel`.  The
induction step splits the survival event at the first time `t₁`: on `{t₁ < τ_U}` the later
coordinates of the killed path are the coordinates of the killed shifted path
(`coordinate_killAtExit_shift`), and the law of the shifted path is supplied by the restart
statement `continuousProcess_killedEvent_inter_shift` proved here, a form of the Markov property
at `t₁` restricted to the `𝓕_{t₁}`-event `{t₁ < τ_U} ∩ {ω t₁ ∈ B}`; on the complement every
coordinate is the cemetery state, matching the absorbing behaviour of the cemetery
(`finiteTimeKernel_cemeterySemigroup_delta`).  Measures on a finite product are compared on boxes.

No Feller property, strong continuity, or regularity of the killed semigroup is claimed, and no
statement here covers a random time.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MarkovProcess

namespace SubMarkovKernelSemigroup

section Dead

variable {beta : Type*} [MeasurableSpace beta] (S : SubMarkovKernelSemigroup beta)



end Dead


section Restart

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)



end Restart


section OrderedMarginals

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)



variable [LocallyCompactSpace alpha]
variable (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)





end OrderedMarginals

end SubMarkovKernelSemigroup

end MarkovProcess


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite-dimensional distributions of the killed process

For the continuous-path process of a conservative Feller semigroup and an open set `U`, this file
identifies every finite-dimensional distribution of the process killed at the exit of `U`
(`killedProcess P hP U hU` of `Killed/Process.lean`, a law on lifetime paths in the carrier `U`)
with the corresponding finite-dimensional distribution of the **cemetery extension of the killed
semigroup** on `U`:

  `(killedProcess x).map (fun ω ↦ fun i : I ↦ coordinate i ω) =
      finiteSetKernel (cemeterySemigroup (killedSemigroup P hP U hU hFeller hK)) I (alive x)`

(`killedProcess_map_finiteEvaluation`), and, at a strictly increasing family of times, the
corresponding statement for `finiteTimeKernel` (`killedProcess_map_coordinates_ordered`).

The proof is by induction on the number of times, along the recursion of `finiteTimeKernel`.  The
induction step splits the survival event at the first time `t₁`: on `{t₁ < τ_U}` the later
coordinates of the killed path are the coordinates of the killed shifted path
(`coordinate_killAtExit_shift`), and the law of the shifted path is supplied by the restart
statement `continuousProcess_killedEvent_inter_shift` proved here, a form of the Markov property
at `t₁` restricted to the `𝓕_{t₁}`-event `{t₁ < τ_U} ∩ {ω t₁ ∈ B}`; on the complement every
coordinate is the cemetery state, matching the absorbing behaviour of the cemetery
(`finiteTimeKernel_cemeterySemigroup_delta`).  Measures on a finite product are compared on boxes.

No Feller property, strong continuity, or regularity of the killed semigroup is claimed, and no
statement here covers a random time.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal




variable {beta : Type*} [MeasurableSpace beta] (S : SubMarkovKernelSemigroup beta)

namespace MarkovProcess.SubMarkovKernelSemigroup

end MarkovProcess.SubMarkovKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup
theorem solution {n : ℕ} (times : FiniteOrderedTimes n) :
    finiteTimeKernel (cemeterySemigroup S) times Cemetery.delta =
      Measure.dirac (fun _ ↦ Cemetery.delta) := by
  induction n with
  | zero =>
      rw [finiteTimeKernel_zero, Kernel.const_apply]
      exact congrArg Measure.dirac (Subsingleton.elim _ _)
  | succ n ih =>
      let : IsMarkovKernel (cemeterySemigroup S (times 0)) :=
        (isConservative_cemeterySemigroup S).isMarkovKernel (times 0)
      let : IsMarkovKernel (finiteTimeKernel (cemeterySemigroup S) times.relativeTail) :=
        (isConservative_cemeterySemigroup S).isMarkovKernel_finiteTimeKernel _ _
      have hprod : (cemeterySemigroup S (times 0) ⊗ₖ
            Kernel.prodMkLeft (Cemetery beta)
              (finiteTimeKernel (cemeterySemigroup S) times.relativeTail))
              Cemetery.delta =
          Measure.dirac (Cemetery.delta, fun _ ↦ Cemetery.delta) := by
        refine Measure.ext fun s hs ↦ ?_
        rw [Kernel.compProd_apply hs, cemeterySemigroup_absorbing,
          lintegral_dirac' _ (Kernel.measurable_kernel_prodMk_left' hs _),
          Kernel.prodMkLeft_apply, ih,
          Measure.dirac_apply' _ (measurable_prodMk_left hs), Measure.dirac_apply' _ hs]
        by_cases hmem : ((Cemetery.delta : Cemetery beta),
            (fun _ ↦ Cemetery.delta : Fin n → Cemetery beta)) ∈ s
        · rw [Set.indicator_of_mem hmem,
            Set.indicator_of_mem (Set.mem_preimage.mpr hmem), Pi.one_apply, Pi.one_apply]
        · rw [Set.indicator_of_notMem hmem]
          exact Set.indicator_of_notMem
            (show (fun _ ↦ Cemetery.delta : Fin n → Cemetery beta) ∉
              Prod.mk (Cemetery.delta : Cemetery beta) ⁻¹' s from fun h ↦ hmem h)
            (1 : (Fin n → Cemetery beta) → ℝ≥0∞)
      rw [finiteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map,
        Kernel.map_apply _ measurable_finCons, hprod, Measure.map_dirac' measurable_finCons _]
      refine congrArg Measure.dirac ?_
      funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · rw [Fin.cons_zero]
      · rw [Fin.cons_succ]
