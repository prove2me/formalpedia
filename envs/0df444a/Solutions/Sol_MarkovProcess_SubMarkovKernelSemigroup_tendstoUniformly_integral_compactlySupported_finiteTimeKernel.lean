-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.tendstoUniformly_integral_compactlySupported_finiteTimeKernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T22:46:14.547865+00:00
-- url     : https://prove2.me/submissions/10856065-6d38-4748-8287-cd967b2b31ce

import Definitions.Def_MarkovProcess_V3H_Feller_BackwardC0Integral_1512e54f
import Definitions.Def_MarkovProcess_V3H_Feller_FiniteTimeConvergence_4d25bc20
import Definitions.Def_MarkovProcess_V3H_FiniteTime_CoordinateProductActiveReduction_0fcd6a29
import Definitions.Def_MarkovProcess_V3H_FiniteTime_FiniteProductCoordinateNormalForm_522d03e6
import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelRestriction_041bf9e5
import Definitions.Def_MarkovProcess_V3H_Semigroup_StrongOperatorLimit_428329b4
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_tendstoUniformly_integral_coordinatePolynomial_finiteTimeKernel

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Convergence of finite-time laws along a family of Feller semigroups

Let `P i` be conservative Feller kernel semigroups whose `C₀` semigroups converge strongly to
that of a conservative Feller kernel semigroup `Q`.  Then, at every fixed finite ordered family
of observation times, the finite-time laws converge, uniformly in the starting point:

* for a coordinate-product term, by reduction to the coordinates carrying a factor and the
  backward `C₀` recursion (`Feller/BackwardC0Convergence.lean`); a term with no active
  coordinate integrates to its coefficient because the finite-time law is a probability measure;
* for a finite coordinate polynomial, by linearity;
* for an arbitrary compactly supported continuous test, by uniform approximation with coordinate
  polynomials (`FiniteTime/FiniteProductCoordinateNormalForm.lean`), the approximation error
  being uniform because the laws are probability measures.

Main results: `tendstoUniformly_integral_coordinateProductTerm_finiteTimeKernel`,
`tendstoUniformly_integral_coordinatePolynomial_finiteTimeKernel`,
`tendstoUniformly_integral_compactlySupported_finiteTimeKernel`.

The observation times are fixed throughout; nothing is asserted for test functions that are only
bounded and continuous, which needs the tightness of the limiting law and is therefore not
uniform in the starting point.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ZeroAtInfty BigOperators CompactlySupported

namespace MarkovProcess

section UniformAlgebra

variable {beta : Type*} {iota : Type*} {l : Filter iota}







end UniformAlgebra

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]
variable {iota : Type*} {l : Filter iota}

section Integrability

omit [LocallyCompactSpace alpha] [T2Space alpha] in
private theorem integrable_coordinateProductTerm
    {n : ℕ} (term : PiContinuousMap.CoordinateProductTerm (Fin n) alpha)
    (mu : Measure (Fin n → alpha)) [IsFiniteMeasure mu] :
    Integrable term.toContinuousMap mu := by
  have hprod : StronglyMeasurable (fun path : Fin n → alpha ↦
      (term.factors.map fun p ↦ p.2 (path p.1)).prod) := by
    induction term.factors with
    | nil => exact stronglyMeasurable_const
    | cons p factors ih =>
        simp only [List.map_cons, List.prod_cons]
        exact ((p.2.measurable.comp (measurable_pi_apply p.1)).stronglyMeasurable).mul ih
  have hfun : (term.toContinuousMap : (Fin n → alpha) → ℝ) = fun path ↦
      term.coefficient * (term.factors.map fun p ↦ p.2 (path p.1)).prod := by
    funext path
    exact PiContinuousMap.CoordinateProductTerm.toContinuousMap_apply term path
  rw [hfun]
  refine Integrable.of_bound (hprod.const_mul term.coefficient).aestronglyMeasurable
    (‖term.coefficient‖ * (term.factors.map fun p ↦ ‖p.2‖).prod) ?_
  filter_upwards [] with path
  rw [norm_mul, List.norm_prod]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  induction term.factors with
  | nil =>
      simp only [List.map_nil, List.prod_nil]
      exact le_rfl
  | cons p factors ih =>
      simp only [List.map_cons, List.prod_cons]
      have all_nonneg : ∀ fs : List (Fin n × C₀(alpha, ℝ)),
          0 ≤ (fs.map fun q ↦ ‖q.2 (path q.1)‖).prod := by
        intro fs
        induction fs with
        | nil => simp only [List.map_nil, List.prod_nil, zero_le_one]
        | cons q fs ih_nonneg =>
            simp only [List.map_cons, List.prod_cons]
            exact mul_nonneg (norm_nonneg _) ih_nonneg
      have hnonneg : 0 ≤ ((factors.map fun p ↦ p.2 (path p.1)).map norm).prod := by
        simpa only [List.map_map, Function.comp_apply] using! all_nonneg factors
      exact mul_le_mul (p.2.toBCF.norm_coe_le_norm (path p.1)) ih hnonneg (norm_nonneg _)

omit [LocallyCompactSpace alpha] [T2Space alpha] in
private theorem integrable_coordinatePolynomial
    {n : ℕ} (terms : List (PiContinuousMap.CoordinateProductTerm (Fin n) alpha))
    (mu : Measure (Fin n → alpha)) [IsFiniteMeasure mu] :
    Integrable (PiContinuousMap.coordinatePolynomial terms) mu := by
  induction terms with
  | nil =>
      simp only [PiContinuousMap.coordinatePolynomial_nil]
      change Integrable (fun _ : Fin n → alpha ↦ (0 : ℝ)) mu
      exact integrable_zero _ _ _
  | cons term terms ih =>
      rw [PiContinuousMap.coordinatePolynomial_cons]
      exact (integrable_coordinateProductTerm term mu).add ih

end Integrability

section ActiveReduction









end ActiveReduction

variable {P : iota → SubMarkovKernelSemigroup alpha} {Q : SubMarkovKernelSemigroup alpha}





section CompactTest

variable [SecondCountableTopology alpha]



end CompactTest

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
# Convergence of finite-time laws along a family of Feller semigroups

Let `P i` be conservative Feller kernel semigroups whose `C₀` semigroups converge strongly to
that of a conservative Feller kernel semigroup `Q`.  Then, at every fixed finite ordered family
of observation times, the finite-time laws converge, uniformly in the starting point:

* for a coordinate-product term, by reduction to the coordinates carrying a factor and the
  backward `C₀` recursion (`Feller/BackwardC0Convergence.lean`); a term with no active
  coordinate integrates to its coefficient because the finite-time law is a probability measure;
* for a finite coordinate polynomial, by linearity;
* for an arbitrary compactly supported continuous test, by uniform approximation with coordinate
  polynomials (`FiniteTime/FiniteProductCoordinateNormalForm.lean`), the approximation error
  being uniform because the laws are probability measures.

Main results: `tendstoUniformly_integral_coordinateProductTerm_finiteTimeKernel`,
`tendstoUniformly_integral_coordinatePolynomial_finiteTimeKernel`,
`tendstoUniformly_integral_compactlySupported_finiteTimeKernel`.

The observation times are fixed throughout; nothing is asserted for test functions that are only
bounded and continuous, which needs the tightness of the limiting law and is therefore not
uniform in the starting point.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ZeroAtInfty BigOperators CompactlySupported




variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]
variable {iota : Type*} {l : Filter iota}



variable {P : iota → SubMarkovKernelSemigroup alpha} {Q : SubMarkovKernelSemigroup alpha}






variable [SecondCountableTopology alpha]

namespace MarkovProcess.SubMarkovKernelSemigroup

end MarkovProcess.SubMarkovKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup
theorem solution
    (hP : ∀ i, (P i).IsFellerKernelSemigroup) (hPc : ∀ i, (P i).IsConservative)
    (hQ : Q.IsFellerKernelSemigroup) (hQc : Q.IsConservative)
    (hconv : ∀ (t : NNReal) (f : C₀(alpha, ℝ)),
      Tendsto (fun i ↦ (hP i).c0Semigroup t f) l (nhds (hQ.c0Semigroup t f)))
    {n : ℕ} (times : FiniteOrderedTimes n) (f : C_c(Fin n → alpha, ℝ)) :
    TendstoUniformly (fun i x ↦ ∫ path, f path ∂finiteTimeKernel (P i) times x)
      (fun x ↦ ∫ path, f path ∂finiteTimeKernel Q times x) l := by
  rw [Metric.tendstoUniformly_iff]
  intro eps heps
  have heps3 : (0 : ℝ) < eps / 3 := by positivity
  obtain ⟨terms, hterms⟩ :=
    PiContinuousMap.exists_coordinateProductTerms_near_compactlySupported f heps3
  have hnear : ∀ path : Fin n → alpha,
      ‖PiContinuousMap.coordinatePolynomial terms path - f path‖ < eps / 3 := by
    intro path
    rw [PiContinuousMap.coordinatePolynomial_apply]
    exact hterms path
  have hApprox : ∀ (R : SubMarkovKernelSemigroup alpha), R.IsConservative → ∀ y : alpha,
      dist (∫ path, PiContinuousMap.coordinatePolynomial terms path ∂finiteTimeKernel R times y)
        (∫ path, f path ∂finiteTimeKernel R times y) ≤ eps / 3 := by
    intro R hRc y
    let : IsProbabilityMeasure (finiteTimeKernel R times y) :=
      hRc.isProbabilityMeasure_finiteTimeLaw R times y
    have hp : Integrable (PiContinuousMap.coordinatePolynomial terms)
        (finiteTimeKernel R times y) := integrable_coordinatePolynomial terms _
    have hf : Integrable (f : (Fin n → alpha) → ℝ) (finiteTimeKernel R times y) :=
      (map_continuous f).integrable_of_hasCompactSupport f.hasCompactSupport
    rw [Real.dist_eq, ← MeasureTheory.integral_sub hp hf]
    calc
      |∫ path, (PiContinuousMap.coordinatePolynomial terms path - f path)
          ∂finiteTimeKernel R times y| ≤ (eps / 3) * (finiteTimeKernel R times y).real Set.univ :=
        MeasureTheory.norm_integral_le_of_norm_le_const
          (ae_of_all _ fun path ↦ (hnear path).le)
      _ = eps / 3 := by
        simp only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one]
  have hpoly := tendstoUniformly_integral_coordinatePolynomial_finiteTimeKernel hP hPc hQ hQc
    hconv times terms
  rw [Metric.tendstoUniformly_iff] at hpoly
  filter_upwards [hpoly (eps / 3) heps3] with i hi x
  have hleft := hApprox Q hQc x
  have hright := hApprox (P i) (hPc i) x
  have hix := hi x
  have htri : dist (∫ path, f path ∂finiteTimeKernel Q times x)
      (∫ path, f path ∂finiteTimeKernel (P i) times x) ≤
      dist (∫ path, f path ∂finiteTimeKernel Q times x)
        (∫ path, PiContinuousMap.coordinatePolynomial terms path
          ∂finiteTimeKernel Q times x) +
      dist (∫ path, PiContinuousMap.coordinatePolynomial terms path
          ∂finiteTimeKernel Q times x)
        (∫ path, PiContinuousMap.coordinatePolynomial terms path
          ∂finiteTimeKernel (P i) times x) +
      dist (∫ path, PiContinuousMap.coordinatePolynomial terms path
          ∂finiteTimeKernel (P i) times x)
        (∫ path, f path ∂finiteTimeKernel (P i) times x) := dist_triangle4 _ _ _ _
  rw [dist_comm] at hleft
  linarith
