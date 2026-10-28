-- Prove2me | solution 1 for MarkovProcess.PiContinuousMap.normalizedCoordinateFactors_evaluation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T15:54:17.447438+00:00
-- url     : https://prove2.me/submissions/b8ed9c4f-a843-400e-a768-b605f927ebe3

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


variable {n : ℕ} {alpha : Type*} [TopologicalSpace alpha]







private theorem prod_update_mul (i : Fin n) (a : ℝ) (v : Fin n → ℝ) :
    ∏ j, Function.update v i (a * v i) j = a * ∏ j, v j := by
  have hfun : Function.update v i (a * v i) =
      fun j ↦ (if i = j then a else 1) * v j := by
    funext j
    by_cases h : i = j
    · subst j
      simp only [Function.update_self, if_pos]
    · simp only [Function.update, h, Ne.symm h, dite_false, if_false, one_mul]
  rw [hfun, Finset.prod_mul_distrib, Fintype.prod_ite_eq]

private theorem evalOptionalFactor_merge (f : C₀(alpha, ℝ))
    (g : Option C₀(alpha, ℝ)) (x : alpha) :
    evalOptionalFactor x (mergeOptionalFactor f g) = f x * evalOptionalFactor x g := by
  cases g with
  | none => simp only [mergeOptionalFactor, evalOptionalFactor, mul_one]
  | some g => rfl


theorem solution
    (factors : List (Fin n × C₀(alpha, ℝ))) (x : Fin n → alpha) :
    (factors.map fun p ↦ p.2 (x p.1)).prod =
      ∏ i, evalOptionalFactor (x i) (normalizedCoordinateFactors factors i) := by
  induction factors with
  | nil => simp only [List.map_nil, List.prod_nil, normalizedCoordinateFactors,
      List.foldr_nil, evalOptionalFactor, Finset.prod_const_one]
  | cons p factors ih =>
      simp only [List.map_cons, List.prod_cons, normalizedCoordinateFactors,
        List.foldr_cons]
      rw [ih]
      let accumulated := normalizedCoordinateFactors factors
      have hEvalUpdate :
          (fun i ↦ evalOptionalFactor (x i)
            (Function.update accumulated p.1
              (mergeOptionalFactor p.2 (accumulated p.1)) i)) =
            Function.update (fun i ↦ evalOptionalFactor (x i) (accumulated i)) p.1
              (p.2 (x p.1) * evalOptionalFactor (x p.1) (accumulated p.1)) := by
        funext i
        by_cases h : p.1 = i
        · subst i
          rw [Function.update_self, Function.update_self, evalOptionalFactor_merge]
        · simp only [Function.update, Ne.symm h, dite_false]
      change p.2 (x p.1) * ∏ i, evalOptionalFactor (x i) (accumulated i) =
        ∏ i, evalOptionalFactor (x i)
          (Function.update accumulated p.1
            (mergeOptionalFactor p.2 (accumulated p.1)) i)
      rw [hEvalUpdate, prod_update_mul]
