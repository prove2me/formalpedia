-- Prove2me | solution 1 for HunterPDE.Shared.gradient_convolution_ae
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-18T17:52:35.059002+00:00
-- url     : https://prove2.me/submissions/2d0d7e68-ed5d-410d-af13-b04d1e018ba7

import Theorems.Thm_HunterPDE_Sobolev_HasWeakDeriv_convolution_testFunction
import Theorems.Thm_HunterPDE_Shared_hasWeakDeriv_partial_of_contDiffOn
import Theorems.Thm_HunterPDE_Shared_HasWeakDeriv_ae_eq
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

open MeasureTheory ContinuousLinearMap HunterPDE.Shared
open scoped Convolution ContDiff
set_option autoImplicit false

theorem solution {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hloc : LocallyIntegrable f volume)
    (g : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : ∀ i, HasWeakDeriv Set.univ (Pi.single i 1) f (g i))
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : IsTestFunction Set.univ ρ) :
    gradient (ρ ⋆[lsmul ℝ ℝ, volume] f) =ᵐ[volume]
      (fun x => ∫ y, ρ y • (WithLp.toLp 2 (fun i => g i (x-y)) :
        EuclideanSpace ℝ (Fin n))) := by
  classical
  have happ (u : EuclideanSpace ℝ (Fin n) → ℝ) (a b : List (Fin n)) :
      iteratedPartial u (a ++ b) = iteratedPartial (iteratedPartial u b) a := by
    induction a with
    | nil => rfl
    | cons i a ih => simp only [List.cons_append, iteratedPartial, ih]
  have hrep (u : EuclideanSpace ℝ (Fin n) → ℝ) (i : Fin n) (r : ℕ) :
      iteratedPartial u (List.replicate r i) =
        (HunterPDE.Sobolev.partialDeriv i)^[r] u := by
    induction r with
    | zero => rfl
    | succ r ih =>
      simp only [List.replicate_succ, iteratedPartial, ih, Function.iterate_succ_apply']
      rfl
  have hword (u : EuclideanSpace ℝ (Fin n) → ℝ) (α : Fin n → ℕ)
      (l : List (Fin n)) :
      iteratedPartial u (l.flatMap (fun i => List.replicate (α i) i)) =
        l.foldr (fun i v => (HunterPDE.Sobolev.partialDeriv i)^[α i] v) u := by
    induction l with
    | nil => rfl
    | cons i l ih => rw [List.flatMap_cons, happ, hrep, ih, List.foldr_cons]
  have hderiv (u : EuclideanSpace ℝ (Fin n) → ℝ) (α : Fin n → ℕ) :
      multiDeriv u α = HunterPDE.Sobolev.iteratedPartial α u := hword u α _
  have hbridge (α : Fin n → ℕ) (u v : EuclideanSpace ℝ (Fin n) → ℝ) :
      HasWeakDeriv Set.univ α u v ↔ HunterPDE.Sobolev.HasWeakDeriv Set.univ α u v := by
    simp only [HasWeakDeriv, HunterPDE.Sobolev.HasWeakDeriv, IsTestFunction,
      HunterPDE.Sobolev.IsTestFunction, hderiv]
  have hc : ContDiff ℝ ∞ (ρ ⋆[lsmul ℝ ℝ, volume] f) :=
    hρ.2.1.contDiff_convolution_left (lsmul ℝ ℝ) hρ.1 hloc
  have hae (i : Fin n) : partialDeriv (ρ ⋆[lsmul ℝ ℝ, volume] f) i =ᵐ[volume]
      (ρ ⋆[lsmul ℝ ℝ, volume] g i) := by
    have hw := HunterPDE.Sobolev.HasWeakDeriv.convolution_testFunction
      ((hbridge _ _ _).mp (hg i)) ρ hρ
    have hcl := hasWeakDeriv_partial_of_contDiffOn isOpen_univ _
      (hc.of_le (by simp)).contDiffOn i
    simpa only [Measure.restrict_univ] using
      hcl.ae_eq isOpen_univ ((hbridge _ _ _).mpr hw)
  have hi (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
      Integrable (fun y => ρ y * g i (x-y)) volume :=
    (hρ.2.1.convolutionExists_left (lsmul ℝ ℝ) hρ.1.continuous
      (locallyIntegrableOn_univ.mp (hg i).2.1) x).integrable
  filter_upwards [ae_all_iff.mpr hae] with x hx
  apply PiLp.ext
  intro i
  have hgrad : (gradient (ρ ⋆[lsmul ℝ ℝ, volume] f) x) i =
      partialDeriv (ρ ⋆[lsmul ℝ ℝ, volume] f) i x := by
    have h := inner_gradient_left (𝕜 := ℝ) (f := ρ ⋆[lsmul ℝ ℝ, volume] f)
      (x := x) (y := EuclideanSpace.single i 1)
    rw [EuclideanSpace.inner_single_right] at h
    simpa only [starRingEnd_apply, star_trivial, one_mul, partialDeriv] using h
  rw [hgrad, hx i, eval_integral_piLp]
  · rfl
  · intro j
    exact hi x j
