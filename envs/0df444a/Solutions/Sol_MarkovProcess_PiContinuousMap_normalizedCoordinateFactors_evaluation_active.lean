-- Prove2me | solution 1 for MarkovProcess.PiContinuousMap.normalizedCoordinateFactors_evaluation_active
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T15:59:57.77895+00:00
-- url     : https://prove2.me/submissions/71ae044d-4084-454c-a994-b9bc978c6a48

import Definitions.Def_MarkovProcess_FiniteTime_CoordinateProductActiveReduction
import Definitions.Def_MarkovProcess_FiniteTime_CoordinateProductNormalization
import Definitions.Def_MarkovProcess_FiniteTime_FiniteProductCoordinateNormalForm
import Definitions.Def_MarkovProcess_FiniteTime_FiniteProductStoneWeierstrass
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MarkovProcess MarkovProcess.PiContinuousMap
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Normalizing finite coordinate products

This file groups every factor of a `CoordinateProductTerm (Fin n) alpha` by its coordinate.
The normalized representation is a function into `Option C₀(alpha, ℝ)`: an active coordinate
contains the single product of all its original factors, while an inactive coordinate is `none`.

Using `none` is essential because `C₀(alpha, ℝ)` generally has no constant-one element.  Scalar
evaluation interprets inactivity as `1 : ℝ`, but the normalization itself never constructs a
spurious `1 : C₀(alpha, ℝ)`.  The resulting evaluation identity is suitable for backward kernel
recursions that branch only over active coordinates.

This is purely algebraic finite-product infrastructure: it involves no measure and no kernel.
-/

open scoped CompactlySupported ZeroAtInfty BigOperators

namespace MarkovProcess.PiContinuousMap

variable {n : ℕ} {alpha : Type*} [TopologicalSpace alpha]

















/-- Inactive coordinates have no manufactured `C₀` unit factor. -/
theorem normalizedCoordinateFactors_eq_none_of_notMem_activeCoordinates
    (factors : List (Fin n × C₀(alpha, ℝ))) {i : Fin n}
    (hi : i ∉ activeCoordinates factors) :
    normalizedCoordinateFactors factors i = none := by
  rw [mem_activeCoordinates_iff, Option.isSome_iff_ne_none] at hi
  exact not_ne_iff.mp hi
end MarkovProcess.PiContinuousMap
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Restricting normalized coordinate products to active coordinates

This file enumerates the active coordinates of a normalized `CoordinateProductTerm`, extracts
their genuine `C₀` factors, and proves that evaluation factors through the corresponding
coordinate restriction.  The restricting function is definitionally the same path operation as
`FiniteOrderedTimes.restrictPath (activeOrderEmbedding factors)` when that finite-time API is in
scope.

If there are no active coordinates, the reduced index type is `Fin 0` and the empty scalar
product is one.  No constant-one element of `C₀` is constructed.  This is purely algebraic
finite-product infrastructure: it involves no measure and no kernel.
-/

open scoped CompactlySupported ZeroAtInfty BigOperators


variable {n : ℕ} {alpha : Type*} [TopologicalSpace alpha]





private theorem eval_activeNormalizedFactor
    (factors : List (Fin n × C₀(alpha, ℝ)))
    (j : Fin (activeCoordinates factors).card) (x : alpha) :
    evalOptionalFactor x
        (normalizedCoordinateFactors factors (activeOrderEmbedding factors j)) =
      activeNormalizedFactor factors j x := by
  have hj : (normalizedCoordinateFactors factors
      (activeOrderEmbedding factors j)).isSome := by
    apply (mem_activeCoordinates_iff factors _).mp
    exact Finset.orderEmbOfFin_mem (activeCoordinates factors) rfl j
  generalize hq : normalizedCoordinateFactors factors
      (activeOrderEmbedding factors j) = q at hj ⊢
  cases q with
  | none => exact Bool.noConfusion hj
  | some f =>
      simp only [evalOptionalFactor, activeNormalizedFactor, hq, Option.get_some]


theorem solution
    (factors : List (Fin n × C₀(alpha, ℝ))) (x : Fin n → alpha) :
    ∏ i, evalOptionalFactor (x i) (normalizedCoordinateFactors factors i) =
      ∏ j, activeNormalizedFactor factors j (x (activeOrderEmbedding factors j)) := by
  let A := activeCoordinates factors
  let v : Fin n → ℝ := fun i ↦
    evalOptionalFactor (x i) (normalizedCoordinateFactors factors i)
  calc
    ∏ i, evalOptionalFactor (x i) (normalizedCoordinateFactors factors i) =
        ∏ i ∈ A, v i := by
      symm
      apply Finset.prod_subset (fun i _ ↦ Finset.mem_univ i)
      intro i _ hi
      have hnone := normalizedCoordinateFactors_eq_none_of_notMem_activeCoordinates
        factors (show i ∉ activeCoordinates factors from hi)
      simp only [v, hnone, evalOptionalFactor]
    _ = ∏ i : A, v i := (Finset.prod_finset_coe v A).symm
    _ = ∏ j, v ((A.orderIsoOfFin rfl) j) := by
      symm
      exact (A.orderIsoOfFin rfl).toEquiv.prod_comp (fun i : A ↦ v i)
    _ = ∏ j, activeNormalizedFactor factors j
          (x (activeOrderEmbedding factors j)) := by
      apply Finset.prod_congr rfl
      intro j _
      simpa only [v, A, activeOrderEmbedding,
        Finset.coe_orderIsoOfFin_apply] using
        (eval_activeNormalizedFactor factors j
          (x (activeOrderEmbedding factors j)))
