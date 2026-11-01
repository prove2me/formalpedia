-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.lintegral_eq_feynmanKacENNReal_add_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:16:04.638792+00:00
-- url     : https://prove2.me/submissions/82ef54f7-2b2d-4db9-9b80-27c60dd42160

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
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_feynmanKac_le
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_measurable_feynmanKacENNReal_joint
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_ofReal_feynmanKac_eq_feynmanKacENNReal
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_integral_sub_feynmanKac_eq_integral_of_norm_le
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_stronglyMeasurable_feynmanKacAdditiveFunctional_canonicalFiltration

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Operators associated with a sub-Markov kernel semigroup

This file constructs the jointly measurable time-space kernel and the
canonical contractive operator families on real `Lᵖ`.  It deliberately makes
no claim here about the operator semigroup laws or strong continuity.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

namespace MarkovProcess

variable {α : Type*} [MeasurableSpace α]

namespace SubMarkovKernelSemigroup

variable (P : SubMarkovKernelSemigroup α)



@[simp]
theorem jointKernel_apply (p : NNReal × α) : P.jointKernel p = P p.1 p.2 :=
  rfl

























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





variable [SecondCountableTopology alpha]



/-- The accumulated potential at a deterministic time is strongly measurable on path space. -/
theorem stronglyMeasurable_feynmanKacAdditiveFunctional {q : alpha → ℝ}
    (hq : Measurable q) (t : NNReal) :
    StronglyMeasurable (feynmanKacAdditiveFunctional q t) :=
  (stronglyMeasurable_feynmanKacAdditiveFunctional_canonicalFiltration hq t).mono
    ((ContinuousPath.canonicalFiltration (alpha := alpha)).le t)



















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

omit [LocallyCompactSpace alpha] in
/-- The Feynman--Kac operator preserves nonnegativity. -/
theorem IsConservative.feynmanKac_nonneg {q : alpha → ℝ} {t : NNReal}
    {f : alpha → ℝ} (hf0 : ∀ y, 0 ≤ f y) (x : alpha) :
    0 ≤ IsConservative.feynmanKac P hP q t f x := by
  exact integral_nonneg fun omega ↦ mul_nonneg (Real.exp_pos _).le (hf0 _)




























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













/-- Finite-time perturbation formula for a bounded nonnegative observable. -/
theorem IsFellerKernelSemigroup.integral_sub_feynmanKac_eq_integral
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    {q : alpha → ℝ} (hq : Measurable q) {C : ℝ}
    (hq0 : ∀ y, 0 ≤ q y) (hqC : ∀ y, q y ≤ C)
    {f : alpha → ℝ} (hf : Measurable f) (hf0 : ∀ y, 0 ≤ f y)
    {D : ℝ} (hfD : ∀ y, f y ≤ D) (t : NNReal) (x : alpha) :
    (∫ y, f y ∂(P t x)) - IsConservative.feynmanKac P hP q t f x =
      ∫ s in (0 : ℝ)..t, ∫ y, q y *
        IsConservative.feynmanKac P hP q (t - Real.toNNReal s) f y
        ∂(P (Real.toNNReal s) x) := by
  apply hFeller.integral_sub_feynmanKac_eq_integral_of_norm_le P hP hK hq hq0 hqC hf
    (fun y ↦ by rw [abs_of_nonneg (hf0 y)]; exact hfD y)











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
    {f : alpha → ℝ≥0∞} (hf : Measurable f) {D : NNReal}
    (hfD : ∀ y, f y ≤ (D : ℝ≥0∞)) (t : NNReal) (x : alpha) :
    (∫⁻ y, f y ∂(P t x)) =
      IsConservative.feynmanKacENNReal P hP q t f x +
        ∫⁻ s in Ioc (0 : ℝ) t, ∫⁻ y, ENNReal.ofReal (q y) *
          IsConservative.feynmanKacENNReal P hP q (t - Real.toNNReal s) f y
          ∂(P (Real.toNNReal s) x) := by
  have hC : 0 ≤ C := (hq0 x).trans (hqC x)
  let g : alpha → ℝ := fun y ↦ (f y).toReal
  let kR : ℝ → ℝ := fun s ↦ ∫ y, q y *
    IsConservative.feynmanKac P hP q (t - Real.toNNReal s) g y
    ∂(P (Real.toNNReal s) x)
  let kE : ℝ → ℝ≥0∞ := fun s ↦ ∫⁻ y, ENNReal.ofReal (q y) *
    IsConservative.feynmanKacENNReal P hP q (t - Real.toNNReal s) f y
    ∂(P (Real.toNNReal s) x)
  have hftop (y : alpha) : f y ≠ ∞ :=
    ne_of_lt ((hfD y).trans_lt ENNReal.coe_lt_top)
  have hg : Measurable g := hf.ennreal_toReal
  have hg0 (y : alpha) : 0 ≤ g y := ENNReal.toReal_nonneg
  have hgD (y : alpha) : g y ≤ D := by
    exact (ENNReal.toReal_le_toReal (hftop y) ENNReal.coe_ne_top).mpr (hfD y)
  have hgf : (fun y ↦ ENNReal.ofReal (g y)) = f := by
    funext y
    exact ENNReal.ofReal_toReal (hftop y)
  have hreal := hFeller.integral_sub_feynmanKac_eq_integral P hP hK hq hq0 hqC
    hg hg0 hgD t x
  have hrealAdd : (∫ y, g y ∂(P t x)) =
      IsConservative.feynmanKac P hP q t g x + ∫ s in (0 : ℝ)..t, kR s := by
    exact (sub_eq_iff_eq_add').mp hreal
  have hkR0 (s : ℝ) : 0 ≤ kR s := by
    dsimp only [kR]
    exact integral_nonneg fun y ↦ mul_nonneg (hq0 y)
      (IsConservative.feynmanKac_nonneg P hP hg0 y)
  have hkpoint (s : ℝ) : ENNReal.ofReal (kR s) = kE s := by
    let u : NNReal := Real.toNNReal s
    let r : NNReal := t - u
    let hMarkovU : IsMarkovKernel (P u) := hP.isMarkovKernel u
    have hterm : Integrable (fun y ↦ q y * IsConservative.feynmanKac P hP q r g y)
        (P u x) := by
      refine Integrable.of_bound
        ((hq.mul (IsConservative.measurable_feynmanKac P hP hq r hg)).stronglyMeasurable
          ).aestronglyMeasurable (C * D) ?_
      exact Eventually.of_forall fun y ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg (hq0 y) (IsConservative.feynmanKac_nonneg P hP hg0 y))]
        exact mul_le_mul (hqC y)
          (IsConservative.feynmanKac_le P hP hq0 hg0 hgD y)
          (IsConservative.feynmanKac_nonneg P hP hg0 y) hC
    change ENNReal.ofReal
      (∫ y, q y * IsConservative.feynmanKac P hP q r g y ∂(P u x)) =
        ∫⁻ y, ENNReal.ofReal (q y) *
          IsConservative.feynmanKacENNReal P hP q r f y ∂(P u x)
    rw [ofReal_integral_eq_lintegral_ofReal hterm
        (Eventually.of_forall fun y ↦ mul_nonneg (hq0 y)
          (IsConservative.feynmanKac_nonneg P hP hg0 y))]
    apply lintegral_congr
    intro y
    rw [ENNReal.ofReal_mul (hq0 y),
      IsConservative.ofReal_feynmanKac_eq_feynmanKacENNReal P hP hq hq0 r hg hg0 hgD y,
      hgf]
  have hkEmeas : Measurable kE := by
    let hFiniteJoint : IsFiniteKernel P.jointKernel := ⟨⟨1, ENNReal.one_lt_top, fun p ↦ by
        rw [jointKernel_apply]
        exact P.measure_univ_le_one p.1 p.2⟩⟩
    let K : Kernel ℝ alpha := Kernel.comap P.jointKernel
      (fun s ↦ (Real.toNNReal s, x)) (measurable_real_toNNReal.prodMk measurable_const)
    have hint : Measurable fun p : ℝ × alpha ↦ ENNReal.ofReal (q p.2) *
        IsConservative.feynmanKacENNReal P hP q
          (t - Real.toNNReal p.1) f p.2 := by
      exact (hq.ennreal_ofReal.comp measurable_snd).mul
        ((IsConservative.measurable_feynmanKacENNReal_joint P hP hq hf).comp
          ((measurable_const.sub (measurable_real_toNNReal.comp measurable_fst)).prodMk
            measurable_snd))
    have hlin := hint.lintegral_kernel_prod_right' (κ := K)
    simpa only [kE, K, Kernel.comap_apply, jointKernel_apply] using hlin
  have hkR_eq_toReal : kR = fun s ↦ (kE s).toReal := by
    funext s
    rw [← hkpoint s, ENNReal.toReal_ofReal (hkR0 s)]
  have hkRmeas : Measurable kR := by
    rw [hkR_eq_toReal]
    exact hkEmeas.ennreal_toReal
  have hkRle (s : ℝ) : kR s ≤ C * D := by
    let u : NNReal := Real.toNNReal s
    let r : NNReal := t - u
    let hMarkovU : IsMarkovKernel (P u) := hP.isMarkovKernel u
    dsimp only [kR]
    calc
      (∫ y, q y * IsConservative.feynmanKac P hP q r g y ∂(P u x)) ≤
          ∫ _y, C * D ∂(P u x) := by
        apply integral_mono_of_nonneg
        · exact Eventually.of_forall fun y ↦ mul_nonneg (hq0 y)
            (IsConservative.feynmanKac_nonneg P hP hg0 y)
        · exact integrable_const (C * D)
        · exact Eventually.of_forall fun y ↦ mul_le_mul (hqC y)
            (IsConservative.feynmanKac_le P hP hq0 hg0 hgD y)
            (IsConservative.feynmanKac_nonneg P hP hg0 y) hC
      _ = C * D := by simp only [integral_const, probReal_univ, one_smul]
  have hkRInt : IntervalIntegrable kR volume (0 : ℝ) t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg]
    refine IntegrableOn.of_bound (by simpa only [uIoc] using
        (measure_Ioc_lt_top : volume (Ioc (0 : ℝ) t) < ∞))
      hkRmeas.stronglyMeasurable.aestronglyMeasurable.restrict (C * D) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s _hs
    rw [Real.norm_eq_abs, abs_of_nonneg (hkR0 s)]
    exact hkRle s
  have hplainInt : Integrable g (P t x) := by
    let hMarkovT : IsMarkovKernel (P t) := hP.isMarkovKernel t
    refine Integrable.of_bound hg.stronglyMeasurable.aestronglyMeasurable D ?_
    exact Eventually.of_forall fun y ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 y)]
      exact hgD y
  have hplain : ENNReal.ofReal (∫ y, g y ∂(P t x)) = ∫⁻ y, f y ∂(P t x) := by
    rw [ofReal_integral_eq_lintegral_ofReal hplainInt (Eventually.of_forall hg0), hgf]
  have hfk : ENNReal.ofReal (IsConservative.feynmanKac P hP q t g x) =
      IsConservative.feynmanKacENNReal P hP q t f x := by
    rw [IsConservative.ofReal_feynmanKac_eq_feynmanKacENNReal P hP hq hq0 t hg hg0 hgD x,
      hgf]
  have hcorr : ENNReal.ofReal (∫ s in (0 : ℝ)..t, kR s) =
      ∫⁻ s in Ioc (0 : ℝ) t, kE s := by
    rw [intervalIntegral.integral_of_le t.coe_nonneg,
      ofReal_integral_eq_lintegral_ofReal
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg).mp hkRInt)
        (Eventually.of_forall hkR0)]
    exact lintegral_congr hkpoint
  have hof := congrArg ENNReal.ofReal hrealAdd
  rw [ENNReal.ofReal_add
    (IsConservative.feynmanKac_nonneg P hP hg0 x) (intervalIntegral.integral_nonneg
      t.coe_nonneg fun s _hs ↦ hkR0 s), hplain, hfk, hcorr] at hof
  exact hof
