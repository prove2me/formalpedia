-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.tendstoUniformly_integral_coordinateProductTerm_finiteTimeKernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:39:47.260034+00:00
-- url     : https://prove2.me/submissions/b7d63e7e-cad3-49f1-8cd4-d0299213dc3f

import Mathlib
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

open Filter Topology
namespace MarkovProcess.Semigroup
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
private theorem p2m_inline_tendsto_apply_of_opNorm_le_one {ι : Type*} {l : Filter ι}
    (T : ι → E →L[ℝ] E) (Tlim : E →L[ℝ] E) (v : ι → E) (w : E)
    (hT : ∀ i, ‖T i‖ ≤ 1)
    (hTlim : Tendsto (fun i ↦ T i w) l (nhds (Tlim w)))
    (hv : Tendsto v l (nhds w)) :
    Tendsto (fun i ↦ T i (v i)) l (nhds (Tlim w)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  filter_upwards [Metric.tendsto_nhds.mp hv (ε / 2) hε2,
    Metric.tendsto_nhds.mp hTlim (ε / 2) hε2] with i hvi hTi
  have hcontract : dist (T i (v i)) (T i w) ≤ dist (v i) w := by
    calc
      dist (T i (v i)) (T i w) ≤ ‖T i‖ * dist (v i) w := (T i).dist_le_opNorm _ _
      _ ≤ 1 * dist (v i) w := mul_le_mul_of_nonneg_right (hT i) dist_nonneg
      _ = dist (v i) w := one_mul _
  calc
    dist (T i (v i)) (Tlim w) ≤ dist (T i (v i)) (T i w) + dist (T i w) (Tlim w) :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hcontract.trans_lt hvi) hTi
    _ = ε := add_halves ε

end MarkovProcess.Semigroup


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Convergence of the backward `C₀` recursion along a family of semigroups

The backward recursion of `Feller/BackwardC0Recursion.lean` evolves a nonempty ordered family of
one-coordinate `C₀` factors through the transitions of one Feller kernel semigroup.  Here the
family of times and the factors are held fixed and the *semigroup* varies along a filter: if the
`C₀` semigroups converge strongly, so does the backward recursion, in the `C₀` norm.  The
induction is one line per step: contractivity makes the outer transition insensitive to the
error accumulated by the inner one.

Since the `C₀` norm is the supremum norm, this is exactly convergence of the coordinate-product
integrals against the finite-time kernels, uniformly in the starting point.

Main results: `p2m_inline_tendsto_backwardC0_of_tendsto_c0Semigroup`,
`tendstoUniformly_integral_coordinateProduct_finiteTimeKernel`.

The factors and the observation times are fixed; nothing is asserted when they vary along the
filter as well, and no rate of convergence is claimed.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Topology
open scoped NNReal ZeroAtInfty BigOperators

namespace MarkovProcess

section Uniform

variable {alpha : Type*} [TopologicalSpace alpha] {iota : Type*} {l : Filter iota}

/-- Convergence in the `C₀` norm is uniform convergence of the evaluated functions. -/
theorem tendstoUniformly_apply_of_tendsto {F : iota → C₀(alpha, ℝ)} {f : C₀(alpha, ℝ)}
    (h : Tendsto F l (nhds f)) : TendstoUniformly (fun i x ↦ F i x) (fun x ↦ f x) l :=
  ZeroAtInftyContinuousMap.tendsto_iff_tendstoUniformly.mp h

end Uniform

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]
variable {iota : Type*} {l : Filter iota}





end SubMarkovKernelSemigroup

end MarkovProcess


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

namespace MarkovProcess

section UniformAlgebra

variable {beta : Type*} {iota : Type*} {l : Filter iota}

/-- A family of constants converges uniformly to that constant. -/
theorem tendstoUniformly_const (c : ℝ) :
    TendstoUniformly (fun (_ : iota) (_ : beta) ↦ c) (fun _ ↦ c) l :=
  tendstoUniformlyOn_univ.mp (tendsto_const_nhds.tendstoUniformlyOn_const Set.univ)

/-- Uniform convergence is preserved by multiplication with a fixed scalar. -/
theorem tendstoUniformly_const_mul {F : iota → beta → ℝ} {f : beta → ℝ}
    (h : TendstoUniformly F f l) (c : ℝ) :
    TendstoUniformly (fun i x ↦ c * F i x) (fun x ↦ c * f x) l :=
  (uniformContinuous_const_smul c).comp_tendstoUniformly h



end UniformAlgebra

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]
variable {iota : Type*} {l : Filter iota}

section Integrability





end Integrability

section ActiveReduction

/-- The increasing enumeration of the active coordinates of a coordinate-product term, read at a
positive cardinality of the active set. -/
private def activeEmbedding {n k : ℕ} (factors : List (Fin n × C₀(alpha, ℝ)))
    (hk : (PiContinuousMap.activeCoordinates factors).card = k + 1) : Fin (k + 1) ↪o Fin n :=
  (Fin.castOrderIso hk.symm).toOrderEmbedding.trans
    (PiContinuousMap.activeOrderEmbedding factors)

/-- The normalized `C₀` factors at the active coordinates, indexed in increasing order. -/
private def activeFactor {n k : ℕ} (factors : List (Fin n × C₀(alpha, ℝ)))
    (hk : (PiContinuousMap.activeCoordinates factors).card = k + 1) :
    Fin (k + 1) → C₀(alpha, ℝ) :=
  fun j ↦ PiContinuousMap.activeNormalizedFactor factors (Fin.cast hk.symm j)

omit [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha] in
/-- A coordinate-product term with no active coordinate integrates to its coefficient. -/
private theorem integral_coordinateProductTerm_eq_coefficient
    {Q : SubMarkovKernelSemigroup alpha} (hQc : Q.IsConservative) {n : ℕ}
    (term : PiContinuousMap.CoordinateProductTerm (Fin n) alpha)
    (hA : PiContinuousMap.activeCoordinates term.factors = ∅)
    (u : FiniteOrderedTimes n) (x : alpha) :
    ∫ path, term.toContinuousMap path ∂finiteTimeKernel Q u x = term.coefficient := by
  let : IsProbabilityMeasure (finiteTimeKernel Q u x) :=
    hQc.isProbabilityMeasure_finiteTimeLaw Q u x
  have hTerm : ∀ path : Fin n → alpha, term.toContinuousMap path = term.coefficient := by
    intro path
    rw [PiContinuousMap.CoordinateProductTerm.toContinuousMap_apply_active]
    simp only [PiContinuousMap.CoordinateProductTerm.activeEvaluation, hA,
      Finset.card_empty, Finset.prod_fin_eq_prod_range, Finset.prod_range_zero, mul_one]
  rw [integral_congr_ae (ae_of_all _ hTerm)]
  simp only [integral_const, probReal_univ, one_smul]

/-- A coordinate-product term with active coordinates integrates to its coefficient times the
backward `C₀` recursion at the active times. -/
private theorem integral_coordinateProductTerm_eq_backwardC0
    {Q : SubMarkovKernelSemigroup alpha} (hQ : Q.IsFellerKernelSemigroup)
    (hQc : Q.IsConservative) {n k : ℕ}
    (term : PiContinuousMap.CoordinateProductTerm (Fin n) alpha)
    (hk : (PiContinuousMap.activeCoordinates term.factors).card = k + 1)
    (u : FiniteOrderedTimes n) (x : alpha) :
    ∫ path, term.toContinuousMap path ∂finiteTimeKernel Q u x =
      term.coefficient * hQ.backwardC0 (u.restrict (activeEmbedding term.factors hk))
        (activeFactor term.factors hk) x := by
  have hg : StronglyMeasurable
      (fun path : Fin (k + 1) → alpha ↦ ∏ i, activeFactor term.factors hk i (path i)) :=
    Finset.stronglyMeasurable_fun_prod Finset.univ fun i _ ↦
      (((activeFactor term.factors hk i).measurable.comp
        (measurable_pi_apply i)).stronglyMeasurable)
  have hpoint : ∀ path : Fin n → alpha, term.toContinuousMap path =
      term.coefficient * ∏ i, activeFactor term.factors hk i
        (FiniteOrderedTimes.restrictPath (activeEmbedding term.factors hk) path i) := by
    intro path
    rw [PiContinuousMap.CoordinateProductTerm.toContinuousMap_apply_active]
    simp only [PiContinuousMap.CoordinateProductTerm.activeEvaluation, activeFactor,
      activeEmbedding, FiniteOrderedTimes.restrictPath, RelEmbedding.coe_trans,
      Function.comp_apply, OrderIso.coe_toOrderEmbedding]
    congr 1
    exact ((Fin.castOrderIso hk.symm).toEquiv.prod_comp
      (fun j ↦ PiContinuousMap.activeNormalizedFactor term.factors j
        (path (PiContinuousMap.activeOrderEmbedding term.factors j)))).symm
  calc
    ∫ path, term.toContinuousMap path ∂finiteTimeKernel Q u x =
        ∫ path, term.coefficient * ∏ i, activeFactor term.factors hk i
          (FiniteOrderedTimes.restrictPath (activeEmbedding term.factors hk) path i)
            ∂finiteTimeKernel Q u x :=
      integral_congr_ae (ae_of_all _ hpoint)
    _ = term.coefficient * ∫ path, (fun p : Fin (k + 1) → alpha ↦
          ∏ i, activeFactor term.factors hk i (p i))
          (FiniteOrderedTimes.restrictPath (activeEmbedding term.factors hk) path)
            ∂finiteTimeKernel Q u x := by
      rw [integral_const_mul]
    _ = term.coefficient * ∫ path, ∏ i, activeFactor term.factors hk i (path i)
          ∂(finiteTimeKernel Q u).map
            (FiniteOrderedTimes.restrictPath (activeEmbedding term.factors hk)) x := by
      rw [Kernel.map_apply _
        (FiniteOrderedTimes.measurable_restrictPath (activeEmbedding term.factors hk))]
      rw [integral_map (FiniteOrderedTimes.measurable_restrictPath
        (activeEmbedding term.factors hk)).aemeasurable hg.aestronglyMeasurable]
    _ = term.coefficient * ∫ path, ∏ i, activeFactor term.factors hk i (path i)
          ∂finiteTimeKernel Q (u.restrict (activeEmbedding term.factors hk)) x := by
      rw [hQc.p2m_embedded_df60a2ab25853e30 Q u (activeEmbedding term.factors hk)]
    _ = term.coefficient * hQ.backwardC0 (u.restrict (activeEmbedding term.factors hk))
          (activeFactor term.factors hk) x := by
      rw [hQ.p2m_embedded_2a9d6bc61fa8399e]

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

namespace MarkovProcess.SubMarkovKernelSemigroup

end MarkovProcess.SubMarkovKernelSemigroup
open Filter MeasureTheory Topology
open scoped NNReal ZeroAtInfty BigOperators
namespace MarkovProcess.SubMarkovKernelSemigroup
variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]
variable {iota : Type*} {l : Filter iota}
private theorem p2m_inline_tendsto_backwardC0_of_tendsto_c0Semigroup
    {P : iota → SubMarkovKernelSemigroup alpha} {Q : SubMarkovKernelSemigroup alpha}
    (hP : ∀ i, (P i).IsFellerKernelSemigroup) (hQ : Q.IsFellerKernelSemigroup)
    (hconv : ∀ (t : NNReal) (f : C₀(alpha, ℝ)),
      Tendsto (fun i ↦ (hP i).c0Semigroup t f) l (nhds (hQ.c0Semigroup t f)))
    {n : ℕ} (times : FiniteOrderedTimes (n + 1)) (factors : Fin (n + 1) → C₀(alpha, ℝ)) :
    Tendsto (fun i ↦ (hP i).backwardC0 times factors) l
      (nhds (hQ.backwardC0 times factors)) := by
  induction n with
  | zero =>
      simpa only [IsFellerKernelSemigroup.backwardC0_zero] using hconv (times 0) (factors 0)
  | succ n ih =>
      simp only [IsFellerKernelSemigroup.backwardC0_succ]
      exact Semigroup.p2m_inline_tendsto_apply_of_opNorm_le_one
        (fun i ↦ (hP i).c0Semigroup (times 0)) (hQ.c0Semigroup (times 0))
        (fun i ↦ factors 0 * (hP i).backwardC0 times.relativeTail (Fin.tail factors))
        (factors 0 * hQ.backwardC0 times.relativeTail (Fin.tail factors))
        (fun i ↦ ((hP i).c0Semigroup).norm_operator_le_one _) (hconv (times 0) _)
        (tendsto_const_nhds.mul (ih times.relativeTail (Fin.tail factors)))

end MarkovProcess.SubMarkovKernelSemigroup

open MarkovProcess.SubMarkovKernelSemigroup
theorem solution
    (hP : ∀ i, (P i).IsFellerKernelSemigroup) (hPc : ∀ i, (P i).IsConservative)
    (hQ : Q.IsFellerKernelSemigroup) (hQc : Q.IsConservative)
    (hconv : ∀ (t : NNReal) (f : C₀(alpha, ℝ)),
      Tendsto (fun i ↦ (hP i).c0Semigroup t f) l (nhds (hQ.c0Semigroup t f)))
    {n : ℕ} (times : FiniteOrderedTimes n)
    (term : PiContinuousMap.CoordinateProductTerm (Fin n) alpha) :
    TendstoUniformly
      (fun i x ↦ ∫ path, term.toContinuousMap path ∂finiteTimeKernel (P i) times x)
      (fun x ↦ ∫ path, term.toContinuousMap path ∂finiteTimeKernel Q times x) l := by
  by_cases hA : (PiContinuousMap.activeCoordinates term.factors).card = 0
  · have hAe : PiContinuousMap.activeCoordinates term.factors = ∅ := Finset.card_eq_zero.mp hA
    have hcoefP : ∀ (i : iota) (y : alpha),
        ∫ path, term.toContinuousMap path ∂finiteTimeKernel (P i) times y = term.coefficient :=
      fun i y ↦ integral_coordinateProductTerm_eq_coefficient (hPc i) term hAe times y
    have hcoefQ : ∀ y : alpha,
        ∫ path, term.toContinuousMap path ∂finiteTimeKernel Q times y = term.coefficient :=
      fun y ↦ integral_coordinateProductTerm_eq_coefficient hQc term hAe times y
    simp only [hcoefP, hcoefQ]
    exact tendstoUniformly_const term.coefficient
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hA
    have hbackP : ∀ (i : iota) (y : alpha),
        ∫ path, term.toContinuousMap path ∂finiteTimeKernel (P i) times y =
          term.coefficient * (hP i).backwardC0
            (times.restrict (activeEmbedding term.factors hk))
            (activeFactor term.factors hk) y :=
      fun i y ↦ integral_coordinateProductTerm_eq_backwardC0 (hP i) (hPc i) term hk times y
    have hbackQ : ∀ y : alpha,
        ∫ path, term.toContinuousMap path ∂finiteTimeKernel Q times y =
          term.coefficient * hQ.backwardC0
            (times.restrict (activeEmbedding term.factors hk))
            (activeFactor term.factors hk) y :=
      fun y ↦ integral_coordinateProductTerm_eq_backwardC0 hQ hQc term hk times y
    simp only [hbackP, hbackQ]
    exact tendstoUniformly_const_mul (tendstoUniformly_apply_of_tendsto
      (p2m_inline_tendsto_backwardC0_of_tendsto_c0Semigroup hP hQ hconv
        (times.restrict (activeEmbedding term.factors hk))
        (activeFactor term.factors hk))) term.coefficient
