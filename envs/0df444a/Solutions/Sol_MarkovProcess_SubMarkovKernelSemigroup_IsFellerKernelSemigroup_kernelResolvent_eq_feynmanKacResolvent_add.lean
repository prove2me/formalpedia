-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.kernelResolvent_eq_feynmanKacResolvent_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:26:05.281175+00:00
-- url     : https://prove2.me/submissions/fe45e693-4df7-4fdc-ba7c-959e2e09b08c

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
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_measurable_feynmanKacENNReal_joint
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_lintegral_eq_feynmanKacENNReal_add_lintegral
import Theorems.Thm_intervalIntegral_lintegral_timeTriangle_sub

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
    {f : alpha → ℝ≥0∞} (hf : Measurable f) {D : NNReal}
    (hfD : ∀ y, f y ≤ (D : ℝ≥0∞)) (lam : ℝ) (x : alpha) :
    P.kernelResolvent lam f x =
      IsConservative.feynmanKacResolvent P hP q lam f x +
        P.kernelResolvent lam (fun y ↦ ENNReal.ofReal (q y) *
          IsConservative.feynmanKacResolvent P hP q lam f y) x := by
  have hC : 0 ≤ C := (hq0 x).trans (hqC x)
  let W : ℝ → ℝ≥0∞ := fun t ↦ ENNReal.ofReal (Real.exp (-lam * t))
  let B : ℝ × ℝ → ℝ≥0∞ := fun p ↦ ∫⁻ y, ENNReal.ofReal (q y) *
    IsConservative.feynmanKacENNReal P hP q (Real.toNNReal p.2) f y
    ∂(P (Real.toNNReal p.1) x)
  let H : ℝ × ℝ → ℝ≥0∞ := fun p ↦ W (p.1 + p.2) * B p
  let hFiniteJoint : IsFiniteKernel P.jointKernel := ⟨⟨1, ENNReal.one_lt_top, fun p ↦ by
    rw [jointKernel_apply]
    exact P.measure_univ_le_one p.1 p.2⟩⟩
  let K : Kernel (ℝ × ℝ) alpha := Kernel.comap P.jointKernel
    (fun p ↦ (Real.toNNReal p.1, x))
    ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_const)
  have hB : Measurable B := by
    have hint : Measurable fun p : (ℝ × ℝ) × alpha ↦ ENNReal.ofReal (q p.2) *
        IsConservative.feynmanKacENNReal P hP q (Real.toNNReal p.1.2) f p.2 := by
      exact (hq.ennreal_ofReal.comp measurable_snd).mul
        ((IsConservative.measurable_feynmanKacENNReal_joint P hP hq hf).comp
          ((measurable_real_toNNReal.comp (measurable_snd.comp measurable_fst)).prodMk
            measurable_snd))
    have hlin := hint.lintegral_kernel_prod_right' (κ := K)
    simpa only [B, K, Kernel.comap_apply, jointKernel_apply] using hlin
  have hW : Measurable W := by
    exact ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable
  have hH : Measurable H := (hW.comp measurable_add).mul hB
  have hsets (t : ℝ) : Ioc (0 : ℝ) t =ᶠ[ae volume] Ioo (0 : ℝ) t := by
    filter_upwards [volume.ae_ne t] with s hst
    apply propext
    constructor
    · intro hs
      exact ⟨hs.1, hs.2.lt_of_ne hst⟩
    · exact fun hs ↦ ⟨hs.1, hs.2.le⟩
  have htriangle :
      (∫⁻ t in Ioi (0 : ℝ), W t *
        ∫⁻ s in Ioc (0 : ℝ) t, ∫⁻ y, ENNReal.ofReal (q y) *
          IsConservative.feynmanKacENNReal P hP q
            (Real.toNNReal t - Real.toNNReal s) f y
          ∂(P (Real.toNNReal s) x)) =
        ∫⁻ s in Ioi (0 : ℝ), ∫⁻ u in Ioi (0 : ℝ), H (s, u) := by
    calc
      (∫⁻ t in Ioi (0 : ℝ), W t *
          ∫⁻ s in Ioc (0 : ℝ) t, ∫⁻ y, ENNReal.ofReal (q y) *
            IsConservative.feynmanKacENNReal P hP q
              (Real.toNNReal t - Real.toNNReal s) f y
            ∂(P (Real.toNNReal s) x)) =
          ∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioo (0 : ℝ) t, H (s, t - s) := by
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro t ht
        change W t *
          (∫⁻ s in Ioc (0 : ℝ) t, ∫⁻ y, ENNReal.ofReal (q y) *
            IsConservative.feynmanKacENNReal P hP q
              (Real.toNNReal t - Real.toNNReal s) f y
            ∂(P (Real.toNNReal s) x)) = ∫⁻ s in Ioo (0 : ℝ) t, H (s, t - s)
        rw [← lintegral_const_mul' (μ := volume.restrict (Ioc (0 : ℝ) t))
          (W t) _ (by dsimp only [W]; finiteness), Measure.restrict_congr_set (hsets t)]
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
        have htime : Real.toNNReal t - Real.toNNReal s = Real.toNNReal (t - s) := by
          apply NNReal.coe_injective
          rw [NNReal.coe_sub (Real.toNNReal_le_toNNReal hs.2.le),
            Real.coe_toNNReal t ht.le, Real.coe_toNNReal s hs.1.le,
            Real.coe_toNNReal (t - s) (sub_nonneg.mpr hs.2.le)]
        dsimp only [H, B]
        rw [← htime]
        congr 2
        ring
      _ = _ := intervalIntegral.lintegral_timeTriangle_sub hH
  have hWadd (s u : ℝ) : W (s + u) = W s * W u := by
    dsimp only [W]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  have hquadrant : (∫⁻ s in Ioi (0 : ℝ), ∫⁻ u in Ioi (0 : ℝ), H (s, u)) =
      P.kernelResolvent lam (fun y ↦ ENNReal.ofReal (q y) *
        IsConservative.feynmanKacResolvent P hP q lam f y) x := by
    unfold SubMarkovKernelSemigroup.kernelResolvent
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro s _hs
    let hMarkovS : IsMarkovKernel (P (Real.toNNReal s)) :=
      hP.isMarkovKernel (Real.toNNReal s)
    have hG : Measurable fun p : ℝ × alpha ↦ W p.1 *
        (ENNReal.ofReal (q p.2) *
          IsConservative.feynmanKacENNReal P hP q (Real.toNNReal p.1) f p.2) := by
      exact (hW.comp measurable_fst).mul
        ((hq.ennreal_ofReal.comp measurable_snd).mul
          ((IsConservative.measurable_feynmanKacENNReal_joint P hP hq hf).comp
            ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)))
    calc
      (∫⁻ u in Ioi (0 : ℝ), H (s, u)) =
          W s * ∫⁻ u in Ioi (0 : ℝ), ∫⁻ y, W u *
            (ENNReal.ofReal (q y) *
              IsConservative.feynmanKacENNReal P hP q (Real.toNNReal u) f y)
            ∂(P (Real.toNNReal s) x) := by
        rw [← lintegral_const_mul' (μ := volume.restrict (Ioi (0 : ℝ)))
          (W s) _ (by dsimp only [W]; finiteness)]
        apply lintegral_congr
        intro u
        dsimp only [H, B]
        rw [hWadd]
        rw [lintegral_const_mul' (W u) _ (by dsimp only [W]; finiteness)]
        simp only [mul_assoc]
      _ = W s * ∫⁻ y, (∫⁻ u in Ioi (0 : ℝ), W u *
              (ENNReal.ofReal (q y) *
                IsConservative.feynmanKacENNReal P hP q (Real.toNNReal u) f y))
            ∂(P (Real.toNNReal s) x) := by
        congr 1
        exact lintegral_lintegral_swap (μ := volume.restrict (Ioi (0 : ℝ)))
          (ν := P (Real.toNNReal s) x) hG.aemeasurable
      _ = W s * ∫⁻ y, ENNReal.ofReal (q y) *
            IsConservative.feynmanKacResolvent P hP q lam f y
            ∂(P (Real.toNNReal s) x) := by
        congr 1
        apply lintegral_congr
        intro y
        unfold IsConservative.feynmanKacResolvent
        rw [← lintegral_const_mul' (μ := volume.restrict (Ioi (0 : ℝ)))
          (ENNReal.ofReal (q y)) _ (by finiteness)]
        apply lintegral_congr
        intro u
        ring
  unfold SubMarkovKernelSemigroup.kernelResolvent IsConservative.feynmanKacResolvent
  have hFKmeas : Measurable fun t : ℝ ↦ W t *
      IsConservative.feynmanKacENNReal P hP q (Real.toNNReal t) f x :=
    hW.mul ((IsConservative.measurable_feynmanKacENNReal_joint P hP hq hf).comp
      (measurable_real_toNNReal.prodMk measurable_const))
  calc
    (∫⁻ t in Ioi (0 : ℝ), W t * ∫⁻ y, f y ∂(P (Real.toNNReal t) x)) =
        ∫⁻ t in Ioi (0 : ℝ), W t *
          (IsConservative.feynmanKacENNReal P hP q (Real.toNNReal t) f x +
            ∫⁻ s in Ioc (0 : ℝ) (Real.toNNReal t), ∫⁻ y, ENNReal.ofReal (q y) *
              IsConservative.feynmanKacENNReal P hP q
                (Real.toNNReal t - Real.toNNReal s) f y
              ∂(P (Real.toNNReal s) x)) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have hslice := hFeller.lintegral_eq_feynmanKacENNReal_add_lintegral P hP hK hq
        hq0 hqC hf hfD (Real.toNNReal t) x
      exact congrArg (fun z ↦ W t * z) (by
        simpa only [Real.coe_toNNReal t ht.le] using hslice)
    _ = (∫⁻ t in Ioi (0 : ℝ), W t *
          IsConservative.feynmanKacENNReal P hP q (Real.toNNReal t) f x) +
        ∫⁻ t in Ioi (0 : ℝ), W t *
          ∫⁻ s in Ioc (0 : ℝ) t, ∫⁻ y, ENNReal.ofReal (q y) *
            IsConservative.feynmanKacENNReal P hP q
              (Real.toNNReal t - Real.toNNReal s) f y
            ∂(P (Real.toNNReal s) x) := by
      rw [← lintegral_add_left (μ := volume.restrict (Ioi (0 : ℝ))) hFKmeas]
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [mul_add, Real.coe_toNNReal t ht.le]
    _ = _ := by
      rw [htriangle, hquadrant]
      simp only [W, SubMarkovKernelSemigroup.kernelResolvent,
        IsConservative.feynmanKacResolvent]
