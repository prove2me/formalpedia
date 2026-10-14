-- Prove2me | solution 1 for HunterPDE.Sobolev.iteratedPartial_convolution_testFunction
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T23:31:35.211005+00:00
-- url     : https://prove2.me/submissions/b0d06440-fa6f-4cee-aefc-a96dfaff3380

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic.Ring

open MeasureTheory ContinuousLinearMap HunterPDE.Sobolev
open scoped Convolution ContDiff
set_option autoImplicit false

namespace WeakConvolutionCalculus

lemma test_partial {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : IsTestFunction Set.univ u) (i : Fin n) :
    IsTestFunction Set.univ (partialDeriv i u) := by
  refine ⟨?_, hu.2.1.fderiv_apply ℝ _, Set.subset_univ _⟩
  exact (hu.1.contDiff_fderiv_apply (m := ∞) (by simp)).comp
    (contDiff_id.prodMk contDiff_const)

lemma test_iterate {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : IsTestFunction Set.univ u) (i : Fin n) (k : ℕ) :
    IsTestFunction Set.univ ((partialDeriv i)^[k] u) := by
  induction k with
  | zero => exact hu
  | succ k ih => simpa only [Function.iterate_succ_apply'] using test_partial ih i

lemma test_fold {n : ℕ} (α : Fin n → ℕ) (l : List (Fin n))
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : IsTestFunction Set.univ u) :
    IsTestFunction Set.univ (l.foldr (fun i v => (partialDeriv i)^[α i] v) u) := by
  induction l with
  | nil => exact hu
  | cons i l ih => exact test_iterate ih i (α i)

lemma partial_convolution {n : ℕ} {u f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : IsTestFunction Set.univ u) (hf : LocallyIntegrable f) (i : Fin n) :
    partialDeriv i (u ⋆[lsmul ℝ ℝ, volume] f) =
      (partialDeriv i u ⋆[lsmul ℝ ℝ, volume] f) := by
  funext x
  unfold partialDeriv
  have hc : ContDiff ℝ 1 u := hu.1.of_le (by simp)
  have hder := hu.2.1.hasFDerivAt_convolution_left (lsmul ℝ ℝ) hc hf x
  rw [hder.fderiv]
  rw [convolution_def, convolution_def]
  have hi := (hu.2.1.fderiv ℝ).convolutionExists_left
    ((lsmul ℝ ℝ).precompL (EuclideanSpace ℝ (Fin n)))
    (hu.1.continuous_fderiv (by simp)) hf x
  rw [ContinuousLinearMap.integral_apply hi]
  rfl

lemma iterate_convolution {n : ℕ} {u f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : IsTestFunction Set.univ u) (hf : LocallyIntegrable f) (i : Fin n) (k : ℕ) :
    (partialDeriv i)^[k] (u ⋆[lsmul ℝ ℝ, volume] f) =
      ((partialDeriv i)^[k] u ⋆[lsmul ℝ ℝ, volume] f) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, partial_convolution (test_iterate hu i k) hf,
      Function.iterate_succ_apply']

lemma fold_convolution {n : ℕ} {u f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : IsTestFunction Set.univ u) (hf : LocallyIntegrable f)
    (α : Fin n → ℕ) (l : List (Fin n)) :
    l.foldr (fun i v => (partialDeriv i)^[α i] v) (u ⋆[lsmul ℝ ℝ, volume] f) =
      (l.foldr (fun i v => (partialDeriv i)^[α i] v) u ⋆[lsmul ℝ ℝ, volume] f) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons]
    rw [ih, iterate_convolution (test_fold α l hu) hf]

end WeakConvolutionCalculus

theorem solution {n : ℕ} (α : Fin n → ℕ)
    {u f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : IsTestFunction Set.univ u) (hf : LocallyIntegrable f) :
    iteratedPartial α (u ⋆[lsmul ℝ ℝ, volume] f) =
      (iteratedPartial α u ⋆[lsmul ℝ ℝ, volume] f) :=
  WeakConvolutionCalculus.fold_convolution hu hf α (List.finRange n)
