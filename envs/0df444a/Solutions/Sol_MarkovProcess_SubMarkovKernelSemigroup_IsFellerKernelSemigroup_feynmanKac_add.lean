-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.feynmanKac_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:08:44.523226+00:00
-- url     : https://prove2.me/submissions/c47f6180-fe5f-466f-8400-c040bd36a5fa

import Definitions.Def_MarkovProcess_V3H_Kernel_Operator_8b41d3bf
import Definitions.Def_MarkovProcess_V3H_Trajectory_DynkinMartingale_970781f3
import Definitions.Def_MarkovProcess_V3H_Trajectory_FeynmanKacFunctional_cc8a1986
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
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
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod
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
import Mathlib.Probability.Martingale.Basic
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
import Theorems.Thm_MarkovProcess_ContinuousPath_condExp_shift_ae_eq_integral_pathKernel_of_restrict_map
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_continuousPathTrajectory_restrict_map_shift
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_feynmanKacAdditiveFunctional_add
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_stronglyMeasurable_feynmanKacAdditiveFunctional_canonicalFiltration

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Deterministic-time conditional expectation for the Feller trajectory

At every physical time, the conditional expectation of a bounded strongly measurable functional
of the shifted canonical Feller trajectory, given the canonical filtration at that time, is the
path-kernel expectation started from the current state.  The proof passes the event-restricted
deterministic restart identity through the generic continuous-path conditional-expectation
bridge.

The time here is deterministic.  The corresponding statement at a finite stopping time is in
`Trajectory/FellerStoppingConditional.lean`, and at a stopping time that may be infinite in
`Trajectory/StoppingLtTop.lean`.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess.SubMarkovKernelSemigroup
noncomputable section
open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

/-- At every physical time, the conditional expectation of a bounded functional of the shifted
Feller trajectory given the canonical filtration is its path-kernel expectation started from the
current state. -/
theorem IsFellerKernelSemigroup.continuousPathTrajectory_condExp_shift
    (P : SubMarkovKernelSemigroup alpha) (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (x : alpha) (s : NNReal)
    (F : ContinuousPath alpha → E) (hF : StronglyMeasurable F)
    (C : ℝ) (hFC : ∀ eta, ‖F eta‖ ≤ C) :
    ((continuousPathTrajectory P hP default) x)[fun omega ↦
        F (ContinuousPath.shift s omega)|
      ContinuousPath.canonicalFiltration (alpha := alpha) s] =ᵐ[
        (continuousPathTrajectory P hP default) x]
      fun omega ↦ ∫ eta, F eta ∂(continuousPathTrajectory P hP default)
        (omega s) := by
  apply ContinuousPath.condExp_shift_ae_eq_integral_pathKernel_of_restrict_map
    (continuousPathTrajectory P hP default) x s
  · exact hFeller.continuousPathTrajectory_restrict_map_shift
      P hP default hK x s
  · exact hF
  · exact hFC

end
end MarkovProcess.SubMarkovKernelSemigroup


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The continuous-path Markov process of a Feller semigroup

This is the entry point of the library: for a conservative sub-Markov kernel semigroup `P` on a
nonempty, locally compact Polish state space it names the continuous-path process
`continuousProcess P hP`, restates under quotable names the properties proved for that process
elsewhere in the library, and proves that it is the unique Markov kernel into continuous paths
with the finite-dimensional distributions of `P`.

Every statement carries the Kolmogorov regularity hypothesis `P.KolmogorovRegular hP`, which is
what gives the dense-time trajectory of `P` a continuous modification.  The shift and restart
statements carry in addition the Feller hypothesis `P.IsFellerKernelSemigroup`; the uniqueness
statements carry neither Feller continuity nor local compactness.

Nothing here asserts a Hunt-process property, and no statement covers a stopping time that can be
infinite.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess

section FinsetEvaluation

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]



end ContinuousPath

end FinsetEvaluation

namespace Kernel

noncomputable section DenseFiniteEvaluation

variable {alpha beta : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [MeasurableSpace beta]



section Identification

variable [T2Space alpha] [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]



end Identification

end DenseFiniteEvaluation

end Kernel

namespace SubMarkovKernelSemigroup

noncomputable section

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)



















variable [LocallyCompactSpace alpha]









variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

/-- Simple Markov property in conditional-expectation form: given the canonical filtration at a
deterministic time, the conditional expectation of a bounded functional of the shifted path is
that functional's expectation under the process started from the current state. -/
theorem IsFellerKernelSemigroup.continuousProcess_condExp_shift
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (x : alpha) (s : NNReal) (F : ContinuousPath alpha → E) (hF : StronglyMeasurable F)
    (C : ℝ) (hFC : ∀ eta, ‖F eta‖ ≤ C) :
    ((continuousProcess P hP) x)[fun omega ↦ F (ContinuousPath.shift s omega)|
        ContinuousPath.canonicalFiltration (alpha := alpha) s] =ᵐ[
      (continuousProcess P hP) x]
      fun omega ↦ ∫ eta, F eta ∂(continuousProcess P hP) (omega s) :=
  hFeller.continuousPathTrajectory_condExp_shift P hP _ hK x s F hF C hFC


















end


end SubMarkovKernelSemigroup

end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Feynman--Kac functionals and semigroups

For the continuous-path process of a conservative Feller semigroup, this file constructs the
Feynman--Kac operators associated with a bounded nonnegative measurable potential.  It proves
measurability and bounds for the accumulated potential and operators, the identity at time zero,
and the Feynman--Kac semigroup law.

Main results: `feynmanKacAdditiveFunctional`,
`stronglyMeasurable_feynmanKacAdditiveFunctional`,
`continuous_feynmanKacAdditiveFunctional`, `feynmanKacAdditiveFunctional_add`,
`IsConservative.feynmanKac`, `IsConservative.feynmanKac_zero`,
`IsConservative.measurable_feynmanKac`, `IsConservative.feynmanKac_nonneg`,
`IsConservative.feynmanKac_le`, `IsConservative.feynmanKac_add_apply`,
`IsConservative.feynmanKac_smul_apply`, and `IsFellerKernelSemigroup.feynmanKac_add`.

The resolvent and perturbation identities are developed in `Trajectory/FeynmanKacResolvent.lean`.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MarkovProcess.SubMarkovKernelSemigroup

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]



omit [MeasurableSpace alpha] [BorelSpace alpha] in
/-- The accumulated potential is unfolded as its path integral. -/
theorem feynmanKacAdditiveFunctional_apply (q : alpha → ℝ) (t : NNReal)
    (omega : ContinuousPath alpha) :
    feynmanKacAdditiveFunctional q t omega =
      ∫ s in (0 : ℝ)..t, q (omega (Real.toNNReal s)) :=
  rfl

variable [SecondCountableTopology alpha]



/-- The accumulated potential at a deterministic time is strongly measurable on path space. -/
theorem stronglyMeasurable_feynmanKacAdditiveFunctional {q : alpha → ℝ}
    (hq : Measurable q) (t : NNReal) :
    StronglyMeasurable (feynmanKacAdditiveFunctional q t) :=
  (stronglyMeasurable_feynmanKacAdditiveFunctional_canonicalFiltration hq t).mono
    ((ContinuousPath.canonicalFiltration (alpha := alpha)).le t)







omit [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] in
/-- The accumulated potential is nonnegative. -/
theorem feynmanKacAdditiveFunctional_nonneg {q : alpha → ℝ} (hq0 : ∀ y, 0 ≤ q y)
    (t : NNReal) (omega : ContinuousPath alpha) :
    0 ≤ feynmanKacAdditiveFunctional q t omega := by
  rw [feynmanKacAdditiveFunctional_apply]
  exact intervalIntegral.integral_nonneg t.coe_nonneg fun s _ ↦ hq0 _











variable [CompleteSpace alpha] [Nonempty alpha] [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)



omit [LocallyCompactSpace alpha] in
/-- The Feynman--Kac operator is unfolded as a path expectation. -/
theorem IsConservative.feynmanKac_apply (q : alpha → ℝ) (t : NNReal)
    (f : alpha → ℝ) (x : alpha) :
    IsConservative.feynmanKac P hP q t f x =
      ∫ omega, Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t)
        ∂(IsConservative.continuousProcess P hP x) :=
  rfl


































end

end MarkovProcess.SubMarkovKernelSemigroup


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Feynman--Kac functionals and semigroups

For the continuous-path process of a conservative Feller semigroup, this file constructs the
Feynman--Kac operators associated with a bounded nonnegative measurable potential.  It proves
measurability and bounds for the accumulated potential and operators, the identity at time zero,
and the Feynman--Kac semigroup law.

Main results: `feynmanKacAdditiveFunctional`,
`stronglyMeasurable_feynmanKacAdditiveFunctional`,
`continuous_feynmanKacAdditiveFunctional`, `feynmanKacAdditiveFunctional_add`,
`IsConservative.feynmanKac`, `IsConservative.feynmanKac_zero`,
`IsConservative.measurable_feynmanKac`, `IsConservative.feynmanKac_nonneg`,
`IsConservative.feynmanKac_le`, `IsConservative.feynmanKac_add_apply`,
`IsConservative.feynmanKac_smul_apply`, and `IsFellerKernelSemigroup.feynmanKac_add`.

The resolvent and perturbation identities are developed in `Trajectory/FeynmanKacResolvent.lean`.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal



variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]





variable [SecondCountableTopology alpha]























variable [CompleteSpace alpha] [Nonempty alpha] [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)




































namespace MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup

end MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
theorem solution (hFeller : P.IsFellerKernelSemigroup)
    (hK : P.KolmogorovRegular hP) {q : alpha → ℝ} (hq : Measurable q)
    {C : ℝ} (hq0 : ∀ y, 0 ≤ q y) (hqC : ∀ y, q y ≤ C)
    (s t : NNReal) {f : alpha → ℝ} (hf : Measurable f) {D : ℝ}
    (hfD : ∀ y, ‖f y‖ ≤ D) (x : alpha) :
    IsConservative.feynmanKac P hP q (s + t) f x =
      IsConservative.feynmanKac P hP q s
        (IsConservative.feynmanKac P hP q t f) x := by
  let W : ContinuousPath alpha → ℝ := fun omega ↦
    Real.exp (-feynmanKacAdditiveFunctional q s omega)
  let F : ContinuousPath alpha → ℝ := fun eta ↦
    Real.exp (-feynmanKacAdditiveFunctional q t eta) * f (eta t)
  let mu : Measure (ContinuousPath alpha) := IsConservative.continuousProcess P hP x
  have hW : StronglyMeasurable[ContinuousPath.canonicalFiltration (alpha := alpha) s] W := by
    have hA : Measurable[ContinuousPath.canonicalFiltration (alpha := alpha) s]
        (fun omega ↦ -feynmanKacAdditiveFunctional q s omega) :=
      (stronglyMeasurable_feynmanKacAdditiveFunctional_canonicalFiltration hq s).measurable.neg
    exact hA.exp.stronglyMeasurable
  have hF : StronglyMeasurable F := by
    have hweight : StronglyMeasurable fun eta : ContinuousPath alpha ↦
        Real.exp (-feynmanKacAdditiveFunctional q t eta) :=
      (stronglyMeasurable_feynmanKacAdditiveFunctional hq t).measurable.neg.exp.stronglyMeasurable
    exact hweight.mul ((hf.comp
      (ContinuousPath.measurable_coordinateProcess (alpha := alpha) t)).stronglyMeasurable)
  have hFbound : ∀ eta : ContinuousPath alpha, ‖F eta‖ ≤ D := by
    intro eta
    dsimp only [F]
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-feynmanKacAdditiveFunctional q t eta) * ‖f (eta t)‖ ≤ 1 * ‖f (eta t)‖ :=
        mul_le_mul_of_nonneg_right
          ((Real.exp_le_one_iff).mpr
            (neg_nonpos.mpr (feynmanKacAdditiveFunctional_nonneg hq0 t eta))) (norm_nonneg _)
      _ ≤ D := by simpa only [one_mul] using hfD _
  have hWFbound : ∀ omega : ContinuousPath alpha,
      ‖W omega * F (ContinuousPath.shift s omega)‖ ≤ D := by
    intro omega
    rw [norm_mul]
    calc
      ‖W omega‖ * ‖F (ContinuousPath.shift s omega)‖ ≤ 1 * ‖F (ContinuousPath.shift s omega)‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        dsimp only [W]
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact (Real.exp_le_one_iff).mpr
          (neg_nonpos.mpr (feynmanKacAdditiveFunctional_nonneg hq0 s omega))
      _ ≤ D := by simpa only [one_mul] using hFbound _
  have hIntFshift : Integrable (fun omega ↦ F (ContinuousPath.shift s omega)) mu :=
    Integrable.of_bound
      (hF.comp_measurable
        (ContinuousPath.measurable_shift_fixed (alpha := alpha) s)).aestronglyMeasurable
      D (Eventually.of_forall fun omega ↦ hFbound _)
  have hIntWF : Integrable (fun omega ↦ W omega * F (ContinuousPath.shift s omega)) mu :=
    Integrable.of_bound
      ((hW.mono ((ContinuousPath.canonicalFiltration (alpha := alpha)).le s)).mul
        (hF.comp_measurable
          (ContinuousPath.measurable_shift_fixed (alpha := alpha) s))).aestronglyMeasurable
      D (Eventually.of_forall hWFbound)
  have hcond := hFeller.continuousProcess_condExp_shift P hP hK x s F hF D hFbound
  have hpull := condExp_mul_of_stronglyMeasurable_left (μ := mu) hW hIntWF hIntFshift
  have htotal : (fun omega ↦
      Real.exp (-feynmanKacAdditiveFunctional q (s + t) omega) * f (omega (s + t))) =
      fun omega ↦ W omega * F (ContinuousPath.shift s omega) := by
    funext omega
    dsimp only [W, F]
    rw [ContinuousPath.shift_apply, feynmanKacAdditiveFunctional_add hq hq0 hqC]
    rw [neg_add, Real.exp_add]
    ring
  rw [IsConservative.feynmanKac_apply, htotal]
  calc
    (∫ omega, W omega * F (ContinuousPath.shift s omega) ∂mu) =
        ∫ omega, mu[fun eta ↦ W eta * F (ContinuousPath.shift s eta)|
          ContinuousPath.canonicalFiltration (alpha := alpha) s] omega ∂mu := by
            rw [integral_condExp ((ContinuousPath.canonicalFiltration (alpha := alpha)).le s)]
    _ = ∫ omega, W omega *
          (∫ eta, F eta ∂IsConservative.continuousProcess P hP (omega s)) ∂mu := by
            refine integral_congr_ae (hpull.trans ?_)
            exact EventuallyEq.mul (EventuallyEq.refl _ _) hcond
    _ = IsConservative.feynmanKac P hP q s
          (IsConservative.feynmanKac P hP q t f) x := by
            rfl
