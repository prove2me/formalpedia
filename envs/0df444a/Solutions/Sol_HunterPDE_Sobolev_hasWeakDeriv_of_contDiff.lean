-- Prove2me | solution 1 for HunterPDE.Sobolev.hasWeakDeriv_of_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T23:00:15.177329+00:00
-- url     : https://prove2.me/submissions/07303820-0c1c-431b-9ae4-1a6b02912755

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace
import Theorems.Thm_HunterPDE_Shared_iteratedPartial_eq_of_perm
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Tactic.Ring

open MeasureTheory HunterPDE.Sobolev
open scoped ContDiff
set_option autoImplicit false

namespace SmoothWeakProof

lemma test_partial {n : ℕ} {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hψ : IsTestFunction Set.univ ψ) (i : Fin n) :
    IsTestFunction Set.univ (partialDeriv i ψ) := by
  refine ⟨?_, hψ.2.1.fderiv_apply ℝ _, Set.subset_univ _⟩
  exact (hψ.1.contDiff_fderiv_apply (m := ∞) (by simp)).comp
    (contDiff_id.prodMk contDiff_const)

lemma smooth_word {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ ∞ u) (l : List (Fin n)) :
    ContDiff ℝ ∞ (HunterPDE.Shared.iteratedPartial u l) := by
  induction l with
  | nil => exact hu
  | cons i l ih =>
    exact (ih.contDiff_fderiv_apply (m := ∞) (by simp)).comp
      (contDiff_id.prodMk contDiff_const)

lemma product_integrable {n : ℕ} {u ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : Continuous u) (hψ : IsTestFunction Set.univ ψ) :
    Integrable (fun x => u x * ψ x) :=
  (hu.mul hψ.1.continuous).integrable_of_hasCompactSupport hψ.2.1.mul_left

lemma word_adjoint {n : ℕ} {u ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ ∞ u) (l : List (Fin n)) (hψ : IsTestFunction Set.univ ψ) :
    (∫ x, HunterPDE.Shared.iteratedPartial u l x * ψ x) =
      (-1 : ℝ) ^ l.length * ∫ x, u x * HunterPDE.Shared.iteratedPartial ψ l.reverse x := by
  induction l generalizing ψ with
  | nil => simp [HunterPDE.Shared.iteratedPartial]
  | cons i l ih =>
    have hv := smooth_word hu l
    have hdψ := test_partial hψ i
    have hdv : ContDiff ℝ ∞ (partialDeriv i (HunterPDE.Shared.iteratedPartial u l)) :=
      (hv.contDiff_fderiv_apply (m := ∞) (by simp)).comp
        (contDiff_id.prodMk contDiff_const)
    have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := volume) (v := EuclideanSpace.single i 1)
      (product_integrable hdv.continuous hψ)
      (product_integrable hv.continuous hdψ)
      (product_integrable hv.continuous hψ)
      (fun x _ => hv.differentiable (by simp) x)
      (fun x _ => hψ.1.differentiable (by simp) x)
    have happ (t : List (Fin n)) :
        HunterPDE.Shared.iteratedPartial ψ (t ++ [i]) =
          HunterPDE.Shared.iteratedPartial (partialDeriv i ψ) t := by
      induction t with
      | nil => rfl
      | cons j t iht => simp only [List.cons_append, HunterPDE.Shared.iteratedPartial, iht]
    change (∫ x, partialDeriv i (HunterPDE.Shared.iteratedPartial u l) x * ψ x) = _
    have hfirst : (∫ x, partialDeriv i (HunterPDE.Shared.iteratedPartial u l) x * ψ x) =
        -(∫ x, HunterPDE.Shared.iteratedPartial u l x * partialDeriv i ψ x) := by
      change (∫ x, HunterPDE.Shared.iteratedPartial u l x * partialDeriv i ψ x) =
        -(∫ x, partialDeriv i (HunterPDE.Shared.iteratedPartial u l) x * ψ x) at hibp
      linarith
    rw [hfirst, ih hdψ, List.reverse_cons, happ, List.length_cons, pow_succ]
    ring

lemma word_bridge {n : ℕ} (α : Fin n → ℕ) (u : EuclideanSpace ℝ (Fin n) → ℝ) :
    iteratedPartial α u = HunterPDE.Shared.multiDeriv u α := by
  unfold iteratedPartial HunterPDE.Shared.multiDeriv HunterPDE.Shared.multiIndexList
  generalize List.finRange n = l
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons, List.flatMap_cons]
    rw [ih]
    generalize List.flatMap (fun i => List.replicate (α i) i) l = t
    induction α i with
    | zero => rfl
    | succ k ihk =>
      simp only [Function.iterate_succ_apply', List.replicate_succ, List.cons_append,
        HunterPDE.Shared.iteratedPartial]
      rw [ihk]
      rfl

end SmoothWeakProof

theorem solution {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) (α : Fin n → ℕ) :
    HasWeakDeriv Set.univ α u (iteratedPartial α u) := by
  refine ⟨hu.continuous.continuousOn.locallyIntegrableOn MeasurableSet.univ, ?_, ?_⟩
  · rw [SmoothWeakProof.word_bridge, HunterPDE.Shared.multiDeriv]
    exact (SmoothWeakProof.smooth_word hu _).continuous.continuousOn.locallyIntegrableOn
      MeasurableSet.univ
  · intro ψ hψ
    simp only [Measure.restrict_univ]
    rw [SmoothWeakProof.word_bridge, HunterPDE.Shared.multiDeriv]
    have h := SmoothWeakProof.word_adjoint hu (HunterPDE.Shared.multiIndexList α) hψ
    have heq : HunterPDE.Shared.iteratedPartial ψ (HunterPDE.Shared.multiIndexList α).reverse =
        iteratedPartial α ψ := by
      rw [SmoothWeakProof.word_bridge, HunterPDE.Shared.multiDeriv]
      funext x
      exact HunterPDE.Shared.iteratedPartial_eq_of_perm isOpen_univ hψ.1.contDiffOn
        (List.reverse_perm _) (Set.mem_univ x)
    have hlen : (HunterPDE.Shared.multiIndexList α).length = ∑ i, α i := by
      simp [HunterPDE.Shared.multiIndexList, List.length_flatMap, List.sum_ofFn,
        ← List.ofFn_eq_map]
    rw [heq, hlen] at h
    exact h
