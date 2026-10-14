-- Prove2me | solution 1 for HunterPDE.Sobolev.iteratedPartial_comp_sub
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T23:32:12.652752+00:00
-- url     : https://prove2.me/submissions/88a56733-1ab0-4d21-aa1a-04edee86a9c3

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Ring

open MeasureTheory ContinuousLinearMap HunterPDE.Sobolev
open scoped ContDiff
set_option autoImplicit false

namespace WeakConvolutionReflection

lemma smooth_partial {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ ∞ u) (i : Fin n) : ContDiff ℝ ∞ (partialDeriv i u) :=
  (hu.contDiff_fderiv_apply (m := ∞) (by simp)).comp
    (contDiff_id.prodMk contDiff_const)

lemma smooth_iterate {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ ∞ u) (i : Fin n) (k : ℕ) :
    ContDiff ℝ ∞ ((partialDeriv i)^[k] u) := by
  induction k with
  | zero => exact hu
  | succ k ih => simpa only [Function.iterate_succ_apply'] using smooth_partial ih i

lemma smooth_fold {n : ℕ} (α : Fin n → ℕ) (l : List (Fin n))
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (l.foldr (fun i v => (partialDeriv i)^[α i] v) u) := by
  induction l with
  | nil => exact hu
  | cons i l ih => exact smooth_iterate ih i (α i)

lemma partial_reflect {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ ∞ u) (i : Fin n) (a : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    partialDeriv i (fun y => a * u (x - y)) =
      fun y => (-a) * partialDeriv i u (x - y) := by
  funext y
  have h := ((hu.differentiable (by simp) (x-y)).hasFDerivAt.comp y
    ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))).const_mul a
  change (fderiv ℝ (fun y => a * (u ∘ HSub.hSub x) y) y) _ = _
  rw [h.fderiv]
  simp [partialDeriv]

lemma iterate_reflect {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ ∞ u) (i : Fin n) (k : ℕ) (a : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (partialDeriv i)^[k] (fun y => a * u (x-y)) =
      fun y => ((-1 : ℝ)^k * a) * ((partialDeriv i)^[k] u) (x-y) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih,
      partial_reflect (smooth_iterate hu i k) i, Function.iterate_succ_apply']
    funext y
    simp only [pow_succ]
    ring

lemma fold_reflect {n : ℕ} (α : Fin n → ℕ) (l : List (Fin n))
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ ∞ u)
    (x : EuclideanSpace ℝ (Fin n)) :
    l.foldr (fun i v => (partialDeriv i)^[α i] v) (fun y => u (x-y)) =
      fun y => (-1 : ℝ)^((l.map α).sum) *
        (l.foldr (fun i v => (partialDeriv i)^[α i] v) u) (x-y) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    rw [ih, iterate_reflect (smooth_fold α l hu) i]
    simp only [pow_add, mul_assoc]

end WeakConvolutionReflection

theorem solution {n : ℕ} (α : Fin n → ℕ)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ ∞ u)
    (x : EuclideanSpace ℝ (Fin n)) :
    iteratedPartial α (fun y => u (x-y)) =
      fun y => (-1 : ℝ)^(∑ i, α i) * iteratedPartial α u (x-y) := by
  have h := WeakConvolutionReflection.fold_reflect α (List.finRange n) hu x
  have hs : ((List.finRange n).map α).sum = ∑ i, α i := by
    simp [← List.ofFn_eq_map, List.sum_ofFn]
  simpa only [iteratedPartial, hs] using h
