-- Prove2me | solution 1 for HunterPDE.Shared.iteratedPartial_sum_coordinate_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T13:26:03.363987+00:00
-- url     : https://prove2.me/submissions/4002823f-5cb3-4834-ab00-27364b06db45

import Definitions.Def_HunterPDE_Shared_WeakDeriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
open HunterPDE.Shared
open scoped ContDiff
set_option autoImplicit false

theorem solution {n : ℕ} {ι : Type*} [Fintype ι] (i : Fin n) (a t : ι → ℝ)
    (e : ι → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (he : ∀ j k, e j (EuclideanSpace.single k 1) =
      (if k = i then t j else 1) • EuclideanSpace.single k 1)
    (u : ι → EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : ∀ j, ContDiff ℝ ∞ (u j)) (l : List (Fin n)) :
    iteratedPartial (fun x => ∑ j, a j * u j (e j x)) l =
      fun x => ∑ j, (a j * t j ^ l.count i) * iteratedPartial (u j) l (e j x) := by
  classical
  have smooth_word {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
      (hu : ContDiff ℝ ∞ u) (l : List (Fin n)) :
      ContDiff ℝ ∞ (iteratedPartial u l) := by
    induction l with
    | nil => exact hu
    | cons i l ih =>
      exact (ih.contDiff_fderiv_apply (m := ∞) (by simp)).comp
        (contDiff_id.prodMk contDiff_const)
  
  have word_linear {n : ℕ}
      (a : ι → ℝ) (u : ι → EuclideanSpace ℝ (Fin n) → ℝ)
      (hu : ∀ j, ContDiff ℝ ∞ (u j)) (l : List (Fin n)) :
      iteratedPartial (fun x => ∑ j, a j * u j x) l =
        fun x => ∑ j, a j * iteratedPartial (u j) l x := by
    classical
    induction l with
    | nil => rfl
    | cons i l ih =>
      simp only [iteratedPartial, ih]
      funext x
      unfold partialDeriv
      have hd (j : ι) := ((smooth_word (hu j) l).differentiable (by simp) x).hasFDerivAt
      have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => (hd j).const_mul (a j))
      rw [hs.fderiv]
      simp
  
  have word_diagonal {n : ℕ} (i : Fin n) (t : ℝ)
      (e : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (he : ∀ k, e (EuclideanSpace.single k 1) =
        (if k = i then t else 1) • EuclideanSpace.single k 1)
      {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ ∞ u)
      (l : List (Fin n)) :
      iteratedPartial (fun x => u (e x)) l =
        fun x => t ^ l.count i * iteratedPartial u l (e x) := by
    classical
    induction l with
    | nil => simp [iteratedPartial]
    | cons k l ih =>
      simp only [iteratedPartial, ih]
      funext x
      have hd := ((smooth_word hu l).differentiable (by simp) (e x)).hasFDerivAt
      have hh := (hd.comp x e.hasFDerivAt).const_mul (t ^ l.count i)
      unfold partialDeriv
      change (fderiv ℝ (fun y => t ^ l.count i * (iteratedPartial u l ∘ e) y) x) _ = _
      rw [hh.fderiv]
      change t ^ l.count i * (fderiv ℝ (iteratedPartial u l) (e x))
        (e (EuclideanSpace.single k 1)) = _
      rw [he, map_smul]
      by_cases hk : k = i
      · subst k
        simp [List.count_cons, pow_succ, mul_assoc, mul_comm, mul_left_comm]
      · simp [hk, List.count_cons]
  
  rw [word_linear a (fun j x => u j (e j x))
    (fun j => by simpa only [Function.comp_def] using (hu j).comp (e j).contDiff) l]
  funext x
  apply Finset.sum_congr rfl
  intro j _
  rw [word_diagonal i (t j) (e j) (he j) (hu j) l]
  simp only [mul_assoc]
