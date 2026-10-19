-- Prove2me | solution 1 for HunterPDE.Sobolev.HasWeakDeriv.translate
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T11:04:56.537979+00:00
-- url     : https://prove2.me/submissions/26814b8f-0b73-431d-bb36-8e5fbc8eb41b

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Group.Integral
open MeasureTheory HunterPDE.Sobolev
set_option autoImplicit false
open scoped ContDiff

namespace SobolevTranslation

lemma locallyIntegrable_translate {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : LocallyIntegrableOn f Set.univ) (a : EuclideanSpace ℝ (Fin n)) :
    LocallyIntegrableOn (fun x => f (x - a)) Set.univ := by
  rw [locallyIntegrableOn_univ] at hf ⊢
  have h := (locallyIntegrable_map_homeomorph (Homeomorph.addRight (-a)) (f := f) (μ := volume)).mp
    (by
      change LocallyIntegrable f (Measure.map (fun x => x + -a) volume)
      rw [(measurePreserving_add_right volume (-a)).map_eq]
      exact hf)
  simpa [Function.comp_def, sub_eq_add_neg] using h

lemma iteratedPartial_add {n : ℕ} (α : Fin n → ℕ)
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (a : EuclideanSpace ℝ (Fin n)) :
    iteratedPartial α (fun x => u (x + a)) = fun x => iteratedPartial α u (x + a) := by
  have hp (i : Fin n) (v : EuclideanSpace ℝ (Fin n) → ℝ) :
      partialDeriv i (fun x => v (x + a)) = fun x => partialDeriv i v (x + a) := by
    funext x
    simp only [partialDeriv, fderiv_comp_add_right]
  have hi (i : Fin n) (j : ℕ) (v : EuclideanSpace ℝ (Fin n) → ℝ) :
      (partialDeriv i)^[j] (fun x => v (x+a)) =
        fun x => ((partialDeriv i)^[j] v) (x+a) := by
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', ih, hp, Function.iterate_succ_apply']
  unfold iteratedPartial
  generalize List.finRange n = l
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons, ih, hi]

end SobolevTranslation

theorem solution {n : ℕ} {α : Fin n → ℕ}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (h : HasWeakDeriv Set.univ α f g) (a : EuclideanSpace ℝ (Fin n)) :
    HasWeakDeriv Set.univ α (fun x => f (x-a)) (fun x => g (x-a)) := by
  refine ⟨SobolevTranslation.locallyIntegrable_translate h.1 a,
    SobolevTranslation.locallyIntegrable_translate h.2.1 a, ?_⟩
  intro φ hφ
  have ht : IsTestFunction Set.univ (fun x => φ (x+a)) :=
    ⟨hφ.1.comp (contDiff_id.add contDiff_const),
      hφ.2.1.comp_homeomorph (Homeomorph.addRight a), Set.subset_univ _⟩
  have he := h.2.2 _ ht
  simp only [Measure.restrict_univ] at he ⊢
  have hleft := integral_add_right_eq_self
    (fun x => g (x-a) * φ x) a (μ := volume)
  have hright := integral_add_right_eq_self
    (fun x => f (x-a) * iteratedPartial α φ x) a (μ := volume)
  simp only [add_sub_cancel_right] at hleft hright
  rw [SobolevTranslation.iteratedPartial_add] at he
  rw [← hleft, ← hright]
  exact he


