-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.integral_sub_feynmanKac_eq_integral_of_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T09:59:39.186437+00:00
-- url     : https://prove2.me/submissions/dcc74ea9-3cda-49eb-9ac0-9e144fa8a2dc

import Definitions.Def_MarkovProcess_V3H_Kernel_Resolvent_f63a7282
import Definitions.Def_MarkovProcess_V3H_Killed_Resolvent_b61459c1
import Definitions.Def_MarkovProcess_V3H_Trajectory_FeynmanKacFunctional_cc8a1986
import Definitions.Def_MarkovProcess_V3H_Trajectory_FeynmanKacResolvent_ed9736ae
import Definitions.Def_MarkovProcess_V3H_Trajectory_ResolventExitDecomposition_db489119
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
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
import Mathlib.MeasureTheory.Integral.ExpDecay
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
import Mathlib.Probability.Martingale.OptionalStopping
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
import Theorems.Thm_MarkovProcess_ContinuousPath_condExp_shift_ae_eq_integral_pathKernel_of_restrict_map
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_continuousPathTrajectory_restrict_map_shift
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_integral_eval_continuousProcess_of_measurable
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_feynmanKacAdditiveFunctional_add
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_one_sub_exp_neg_feynmanKacAdditiveFunctional
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_stronglyMeasurable_feynmanKacAdditiveFunctional_canonicalFiltration
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_stronglyMeasurable_feynmanKacAdditiveFunctional_joint

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Canonical continuous-path space

This file provides the compact-open space of continuous paths on nonnegative real time, its
coordinate process, and the filtration generated by coordinates up to each time. It constructs
no probability law and makes no stochastic-process association or path-regularity claim.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

namespace MarkovProcess



namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]























/-- The time-`t` coordinate is measurable for the canonical filtration at time `t`. -/
theorem measurable_coordinateProcess_canonicalFiltration
    [MeasurableSpace alpha] [BorelSpace alpha] (t : NNReal) :
    Measurable[canonicalFiltration (alpha := alpha) t]
      (coordinateProcess (alpha := alpha) t) := by
  apply Measurable.of_comap_le
  exact le_iSup_of_le (⟨t, Set.mem_Iic.mpr le_rfl⟩ : Set.Iic t) le_rfl

end ContinuousPath

end MarkovProcess


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





omit [SecondCountableTopology alpha] in
/-- The accumulated potential is monotone in time for a nonnegative potential. -/
theorem feynmanKacAdditiveFunctional_mono {q : alpha → ℝ} (hq : Measurable q)
    {C : ℝ} (hq0 : ∀ y, 0 ≤ q y) (hqC : ∀ y, q y ≤ C)
    {s t : NNReal} (hst : s ≤ t) (omega : ContinuousPath alpha) :
    feynmanKacAdditiveFunctional q s omega ≤ feynmanKacAdditiveFunctional q t omega := by
  rw [← add_tsub_cancel_of_le hst,
    feynmanKacAdditiveFunctional_add hq hq0 hqC]
  exact le_add_of_nonneg_right
    (feynmanKacAdditiveFunctional_nonneg hq0 (t - s) (ContinuousPath.shift s omega))

omit [SecondCountableTopology alpha] in
/-- The increment of the accumulated potential is the accumulated potential of the shifted
path. -/
theorem feynmanKacAdditiveFunctional_sub {q : alpha → ℝ} (hq : Measurable q)
    {C : ℝ} (hq0 : ∀ y, 0 ≤ q y) (hqC : ∀ y, q y ≤ C)
    {s t : NNReal} (hst : s ≤ t) (omega : ContinuousPath alpha) :
    feynmanKacAdditiveFunctional q t omega - feynmanKacAdditiveFunctional q s omega =
      feynmanKacAdditiveFunctional q (t - s) (ContinuousPath.shift s omega) := by
  have hadd := feynmanKacAdditiveFunctional_add hq hq0 hqC s (t - s) omega
  rw [add_tsub_cancel_of_le hst] at hadd
  linarith only [hadd]



variable [CompleteSpace alpha] [Nonempty alpha] [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)







omit [LocallyCompactSpace alpha] in
/-- The Feynman--Kac operator of a bounded measurable function is measurable in the starting
point. -/
theorem IsConservative.measurable_feynmanKac {q : alpha → ℝ} (hq : Measurable q)
    (t : NNReal) {f : alpha → ℝ} (hf : Measurable f) :
    Measurable (IsConservative.feynmanKac P hP q t f) := by
  have hpath : StronglyMeasurable (fun omega : ContinuousPath alpha ↦
      Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t)) :=
    (((stronglyMeasurable_feynmanKacAdditiveFunctional hq t).measurable.neg.exp).mul
      (hf.comp (ContinuousPath.measurable_coordinateProcess (alpha := alpha) t))).stronglyMeasurable
  exact hpath.integral_kernel.measurable






























end

end MarkovProcess.SubMarkovKernelSemigroup


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Feynman--Kac resolvents

This file Laplace-transforms the nonnegative extended-real Feynman--Kac operators and proves their
path-occupation formula, comparison with killed resolvents, and perturbation identities against
the unperturbed kernel resolvent.

Main results: `IsConservative.feynmanKacResolvent`,
`IsConservative.feynmanKacResolvent_eq_lintegral_path`,
`IsConservative.killedResolvent_le_feynmanKacResolvent`,
`IsFellerKernelSemigroup.integral_sub_feynmanKac_eq_integral_of_norm_le`,
`IsFellerKernelSemigroup.kernelResolvent_eq_feynmanKacResolvent_add`, and
`IsFellerKernelSemigroup.feynmanKacResolvent_eq_kernelResolvent_sub`.

No uniqueness statement for the associated resolvent equation is asserted.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MarkovProcess.SubMarkovKernelSemigroup

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [CompleteSpace alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

























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
# Feynman--Kac resolvents

This file Laplace-transforms the nonnegative extended-real Feynman--Kac operators and proves their
path-occupation formula, comparison with killed resolvents, and perturbation identities against
the unperturbed kernel resolvent.

Main results: `IsConservative.feynmanKacResolvent`,
`IsConservative.feynmanKacResolvent_eq_lintegral_path`,
`IsConservative.killedResolvent_le_feynmanKacResolvent`,
`IsFellerKernelSemigroup.integral_sub_feynmanKac_eq_integral_of_norm_le`,
`IsFellerKernelSemigroup.kernelResolvent_eq_feynmanKacResolvent_add`, and
`IsFellerKernelSemigroup.feynmanKacResolvent_eq_kernelResolvent_sub`.

No uniqueness statement for the associated resolvent equation is asserted.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal



variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [CompleteSpace alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)











namespace MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup

end MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
theorem solution
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    {q : alpha → ℝ} (hq : Measurable q) {C : ℝ}
    (hq0 : ∀ y, 0 ≤ q y) (hqC : ∀ y, q y ≤ C)
    {f : alpha → ℝ} (hf : Measurable f)
    {D : ℝ} (hfD : ∀ y, |f y| ≤ D) (t : NNReal) (x : alpha) :
    (∫ y, f y ∂(P t x)) - IsConservative.feynmanKac P hP q t f x =
      ∫ s in (0 : ℝ)..t, ∫ y, q y *
        IsConservative.feynmanKac P hP q (t - Real.toNNReal s) f y
        ∂(P (Real.toNNReal s) x) := by
  have hC : 0 ≤ C := (hq0 x).trans (hqC x)
  let mu : Measure (ContinuousPath alpha) := IsConservative.continuousProcess P hP x
  let H : ℝ × ContinuousPath alpha → ℝ := fun p ↦
    q (p.2 (Real.toNNReal p.1)) *
      Real.exp (-(feynmanKacAdditiveFunctional q t p.2 -
        feynmanKacAdditiveFunctional q (Real.toNNReal p.1) p.2)) * f (p.2 t)
  have hevalJoint : Measurable fun p : ℝ × ContinuousPath alpha ↦
      p.2 (Real.toNNReal p.1) :=
    (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hAs : Measurable fun p : ℝ × ContinuousPath alpha ↦
      feynmanKacAdditiveFunctional q (Real.toNNReal p.1) p.2 :=
    (stronglyMeasurable_feynmanKacAdditiveFunctional_joint hq).measurable.comp
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hAt : Measurable fun p : ℝ × ContinuousPath alpha ↦
      feynmanKacAdditiveFunctional q t p.2 :=
    (stronglyMeasurable_feynmanKacAdditiveFunctional hq t).measurable.comp measurable_snd
  have hH : StronglyMeasurable H := by
    exact (((hq.comp hevalJoint).mul ((hAt.sub hAs).neg.exp)).mul
      ((hf.comp (ContinuousPath.measurable_coordinateProcess (alpha := alpha) t)).comp
        measurable_snd)).stronglyMeasurable
  have hD0 : 0 ≤ D := (abs_nonneg (f x)).trans (hfD x)
  have hHbound (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (t : ℝ))
      (omega : ContinuousPath alpha) : ‖H (s, omega)‖ ≤ C * D := by
    have hsNN : Real.toNNReal s ≤ t := Real.toNNReal_le_iff_le_coe.mpr hs.2
    have hAdiff : 0 ≤ feynmanKacAdditiveFunctional q t omega -
        feynmanKacAdditiveFunctional q (Real.toNNReal s) omega :=
      sub_nonneg.mpr (feynmanKacAdditiveFunctional_mono hq hq0 hqC hsNN omega)
    dsimp only [H]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hq0 _),
      abs_of_pos (Real.exp_pos _)]
    calc
      q (omega (Real.toNNReal s)) * Real.exp (-_) * |f (omega t)| ≤
          C * 1 * D := by
        exact mul_le_mul
          (mul_le_mul (hqC _)
            ((Real.exp_le_one_iff).mpr (neg_nonpos.mpr hAdiff))
            (Real.exp_pos _).le hC) (hfD _) (abs_nonneg _) (mul_nonneg hC zero_le_one)
      _ = C * D := by ring
  have hProdInt : Integrable (Function.uncurry fun (s : ℝ)
      (omega : ContinuousPath alpha) ↦ H (s, omega))
      ((volume.restrict (Ioc (0 : ℝ) t)).prod mu) := by
    refine Integrable.of_bound hH.aestronglyMeasurable (C * D) ?_
    change ∀ᵐ p : ℝ × ContinuousPath alpha
      ∂((volume.restrict (Ioc (0 : ℝ) t)).prod mu), ‖H p‖ ≤ C * D
    rw [Measure.ae_prod_iff_ae_ae (measurableSet_le hH.norm.measurable measurable_const)]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact Eventually.of_forall fun omega ↦ hHbound s ⟨hs.1.le, hs.2⟩ omega
  have hInner (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (t : ℝ)) :
      ∫ omega, H (s, omega) ∂mu =
        ∫ y, q y * IsConservative.feynmanKac P hP q
          (t - Real.toNNReal s) f y ∂(P (Real.toNNReal s) x) := by
    let u : NNReal := Real.toNNReal s
    let r : NNReal := t - u
    let W : ContinuousPath alpha → ℝ := fun omega ↦ q (omega u)
    let F : ContinuousPath alpha → ℝ := fun eta ↦
      Real.exp (-feynmanKacAdditiveFunctional q r eta) * f (eta r)
    have hu : u ≤ t := Real.toNNReal_le_iff_le_coe.mpr hs.2
    have hW : StronglyMeasurable[ContinuousPath.canonicalFiltration (alpha := alpha) u] W :=
      (hq.comp (ContinuousPath.measurable_coordinateProcess_canonicalFiltration
        (alpha := alpha) u)).stronglyMeasurable
    have hF : StronglyMeasurable F := by
      exact (((stronglyMeasurable_feynmanKacAdditiveFunctional hq r).measurable.neg.exp).mul
        (hf.comp (ContinuousPath.measurable_coordinateProcess
          (alpha := alpha) r))).stronglyMeasurable
    have hFbound : ∀ eta : ContinuousPath alpha, ‖F eta‖ ≤ D := by
      intro eta
      dsimp only [F]
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact (mul_le_mul_of_nonneg_right
        ((Real.exp_le_one_iff).mpr
          (neg_nonpos.mpr (feynmanKacAdditiveFunctional_nonneg hq0 r eta))) (abs_nonneg _)).trans
        (by simpa only [one_mul] using hfD _)
    have hIntFshift : Integrable (fun omega ↦ F (ContinuousPath.shift u omega)) mu :=
      Integrable.of_bound
        (((hF.comp_measurable (ContinuousPath.measurable_shift_fixed (alpha := alpha) u))
          ).aestronglyMeasurable) D (Eventually.of_forall fun omega ↦ hFbound _)
    have hIntWF : Integrable (fun omega ↦ W omega * F (ContinuousPath.shift u omega)) mu := by
      refine Integrable.of_bound
        ((((hW.mono ((ContinuousPath.canonicalFiltration (alpha := alpha)).le u)).mul
          (hF.comp_measurable (ContinuousPath.measurable_shift_fixed (alpha := alpha) u)))
          ).aestronglyMeasurable) (C * D) ?_
      exact Eventually.of_forall fun omega ↦ by
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hq0 _)]
        exact mul_le_mul (hqC _) (hFbound _) (norm_nonneg _) hC
    have hcond := hFeller.continuousProcess_condExp_shift P hP hK x u F hF D hFbound
    have hpull := condExp_mul_of_stronglyMeasurable_left (μ := mu) hW hIntWF hIntFshift
    have hfactor : (fun omega ↦ H (s, omega)) =
        fun omega ↦ W omega * F (ContinuousPath.shift u omega) := by
      funext omega
      dsimp only [H, W, F, u, r]
      rw [ContinuousPath.shift_apply, add_tsub_cancel_of_le hu,
        feynmanKacAdditiveFunctional_sub hq hq0 hqC hu]
      ring
    rw [hfactor]
    calc
      (∫ omega, W omega * F (ContinuousPath.shift u omega) ∂mu) =
          ∫ omega, mu[fun eta ↦ W eta * F (ContinuousPath.shift u eta)|
            ContinuousPath.canonicalFiltration (alpha := alpha) u] omega ∂mu := by
              rw [integral_condExp ((ContinuousPath.canonicalFiltration (alpha := alpha)).le u)]
      _ = ∫ omega, W omega *
            (∫ eta, F eta ∂IsConservative.continuousProcess P hP (omega u)) ∂mu := by
              refine integral_congr_ae (hpull.trans ?_)
              exact EventuallyEq.mul (EventuallyEq.refl _ _) hcond
      _ = ∫ omega, q (omega u) * IsConservative.feynmanKac P hP q r f (omega u) ∂mu := by
            rfl
      _ = ∫ y, q y * IsConservative.feynmanKac P hP q r f y ∂(P u x) := by
            simpa only [mu] using!
              (hFeller.integral_eval_continuousProcess_of_measurable P hP hK u x
                (hq.mul (IsConservative.measurable_feynmanKac P hP hq r hf)))
      _ = ∫ y, q y * IsConservative.feynmanKac P hP q
            (t - Real.toNNReal s) f y ∂(P (Real.toNNReal s) x) := by rfl
  have hPath : (∫ omega, f (omega t) ∂mu) -
      IsConservative.feynmanKac P hP q t f x =
        ∫ omega, (∫ s in (0 : ℝ)..t, H (s, omega)) ∂mu := by
    have hPlain : Integrable (fun omega : ContinuousPath alpha ↦ f (omega t)) mu :=
      Integrable.of_bound
        (((hf.comp (ContinuousPath.measurable_coordinateProcess
          (alpha := alpha) t)).stronglyMeasurable
          ).aestronglyMeasurable) D (Eventually.of_forall fun omega ↦ by
            rw [Real.norm_eq_abs]
            exact hfD _)
    have hWeighted : Integrable (fun omega : ContinuousPath alpha ↦
        Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t)) mu :=
      have hmeasWeighted : StronglyMeasurable fun omega : ContinuousPath alpha ↦
          Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t) := by
        have hmeas : Measurable fun omega : ContinuousPath alpha ↦
            Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t) :=
          ((stronglyMeasurable_feynmanKacAdditiveFunctional hq t).measurable.neg.exp).mul
            (hf.comp (ContinuousPath.measurable_coordinateProcess (alpha := alpha) t))
        exact hmeas.stronglyMeasurable
      Integrable.of_bound hmeasWeighted.aestronglyMeasurable D (Eventually.of_forall fun omega ↦ by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
          exact (mul_le_mul_of_nonneg_right
            ((Real.exp_le_one_iff).mpr
              (neg_nonpos.mpr (feynmanKacAdditiveFunctional_nonneg hq0 t omega)))
              (abs_nonneg _)).trans
            (by simpa only [one_mul] using hfD _))
    change (∫ omega, f (omega t) ∂mu) -
      (∫ omega, Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t) ∂mu) = _
    rw [← integral_sub hPlain hWeighted]
    refine integral_congr_ae (Eventually.of_forall fun omega ↦ ?_)
    change f (omega t) - Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t) =
      ∫ s in (0 : ℝ)..t, H (s, omega)
    have halg : f (omega t) - Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t) =
        (1 - Real.exp (-feynmanKacAdditiveFunctional q t omega)) * f (omega t) := by ring
    rw [halg, one_sub_exp_neg_feynmanKacAdditiveFunctional hq hq0 hqC,
      ← intervalIntegral.integral_mul_const]
  have hEval := hFeller.integral_eval_continuousProcess_of_measurable P hP hK t x hf
  calc
    (∫ y, f y ∂(P t x)) - IsConservative.feynmanKac P hP q t f x =
        (∫ omega, f (omega t) ∂mu) - IsConservative.feynmanKac P hP q t f x := by
          rw [hEval]
    _ = ∫ omega, (∫ s in (0 : ℝ)..t, H (s, omega)) ∂mu := hPath
    _ =
        ∫ s in (0 : ℝ)..t, ∫ omega, H (s, omega) ∂mu := by
          calc
            (∫ omega, (∫ s in (0 : ℝ)..t, H (s, omega)) ∂mu) =
                ∫ omega, (∫ s in Ioc (0 : ℝ) t, H (s, omega)) ∂mu := by
                  refine integral_congr_ae (Eventually.of_forall fun omega ↦ ?_)
                  exact intervalIntegral.integral_of_le t.coe_nonneg
            _ = ∫ s in Ioc (0 : ℝ) t, ∫ omega, H (s, omega) ∂mu :=
              (integral_integral_swap hProdInt).symm
            _ = ∫ s in (0 : ℝ)..t, ∫ omega, H (s, omega) ∂mu :=
              (intervalIntegral.integral_of_le t.coe_nonneg).symm
    _ = ∫ s in (0 : ℝ)..t, ∫ y, q y *
          IsConservative.feynmanKac P hP q (t - Real.toNNReal s) f y
          ∂(P (Real.toNNReal s) x) := by
            refine intervalIntegral.integral_congr fun s hs ↦ ?_
            rw [uIcc_of_le t.coe_nonneg] at hs
            exact hInner s hs
