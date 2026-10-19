-- Prove2me | solution 1 for HunterPDE.Shared.hasWeakDeriv_multiDeriv_of_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-18T16:38:19.751778+00:00
-- url     : https://prove2.me/submissions/fde4b0c1-4821-4e1f-91dc-5aa05cbfb4c9

import Theorems.Thm_HunterPDE_Shared_contDiffOn_iteratedPartial
import Theorems.Thm_HunterPDE_Shared_iteratedPartial_eq_of_perm
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Definitions.Def_HunterPDE_Shared_WeakDeriv
import Mathlib.Tactic.Ring

open MeasureTheory HunterPDE.Shared
open scoped ContDiff
set_option autoImplicit false

theorem solution {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiffOn ℝ ∞ f Ω) (α : Fin n → ℕ) :
    HasWeakDeriv Ω α f (multiDeriv f α) := by
  have ht {ψ : EuclideanSpace ℝ (Fin n) → ℝ} (hψ : IsTestFunction Ω ψ)
      (i : Fin n) : IsTestFunction Ω (partialDeriv ψ i) := by
    refine ⟨?_, hψ.2.1.fderiv_apply ℝ _, (tsupport_fderiv_apply_subset ℝ _).trans hψ.2.2⟩
    exact (hψ.1.contDiff_fderiv_apply (m := ∞) (by simp)).comp
      (contDiff_id.prodMk contDiff_const)
  have hp (g ψ : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContinuousOn g Ω)
      (hψ : IsTestFunction Ω ψ) : Integrable (fun x => g x * ψ x) := by
    have hc : Continuous (fun x => g x * ψ x) :=
      (hg.mul hψ.1.continuous.continuousOn).continuous_of_tsupport_subset hΩ
        (tsupport_mul_subset_right.trans hψ.2.2)
    exact hc.integrable_of_hasCompactSupport hψ.2.1.mul_left
  have he (g ψ : EuclideanSpace ℝ (Fin n) → ℝ) (hψ : IsTestFunction Ω ψ) :
      (∫ x in Ω, g x * ψ x) = ∫ x, g x * ψ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hψ.2.2 h)), mul_zero]
  have hadj (l : List (Fin n)) (ψ : EuclideanSpace ℝ (Fin n) → ℝ)
      (hψ : IsTestFunction Ω ψ) :
      (∫ x in Ω, iteratedPartial f l x * ψ x) =
        (-1 : ℝ) ^ l.length * ∫ x in Ω, f x * iteratedPartial ψ l.reverse x := by
    induction l generalizing ψ with
    | nil => simp [iteratedPartial]
    | cons i l ih =>
      have hv := contDiffOn_iteratedPartial hΩ hf l
      have hdv := contDiffOn_iteratedPartial hΩ hf (i :: l)
      have hdψ := ht hψ i
      have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (μ := volume) (v := EuclideanSpace.single i 1)
        (hp _ _ hdv.continuousOn hψ) (hp _ _ hv.continuousOn hdψ)
        (hp _ _ hv.continuousOn hψ)
        (fun x hx => (hv.differentiableOn (by simp) x (hψ.2.2 hx)).differentiableAt
          (hΩ.mem_nhds (hψ.2.2 hx)))
        (fun x _ => hψ.1.differentiable (by simp) x)
      have hfirst : (∫ x in Ω, partialDeriv (iteratedPartial f l) i x * ψ x) =
          -(∫ x in Ω, iteratedPartial f l x * partialDeriv ψ i x) := by
        rw [he _ _ hψ, he _ _ hdψ]
        change (∫ x, iteratedPartial f l x * partialDeriv ψ i x) =
          -(∫ x, partialDeriv (iteratedPartial f l) i x * ψ x) at hibp
        linarith
      have happ (t : List (Fin n)) :
          iteratedPartial ψ (t ++ [i]) = iteratedPartial (partialDeriv ψ i) t := by
        induction t with
        | nil => rfl
        | cons j t iht => simp only [List.cons_append, iteratedPartial, iht]
      change (∫ x in Ω, partialDeriv (iteratedPartial f l) i x * ψ x) = _
      rw [hfirst, ih _ hdψ, List.reverse_cons, happ, List.length_cons, pow_succ]
      ring
  refine ⟨hf.continuousOn.locallyIntegrableOn hΩ.measurableSet,
    (contDiffOn_iteratedPartial hΩ hf (multiIndexList α)).continuousOn.locallyIntegrableOn
      hΩ.measurableSet, ?_⟩
  intro ψ hψ
  have h := hadj (multiIndexList α) ψ hψ
  have hlen : (multiIndexList α).length = ∑ i, α i := by
    simp [multiIndexList, List.length_flatMap, List.sum_ofFn, ← List.ofFn_eq_map]
  have heq : ∀ x ∈ Ω, iteratedPartial ψ (multiIndexList α).reverse x = multiDeriv ψ α x :=
    iteratedPartial_eq_of_perm hΩ hψ.1.contDiffOn (List.reverse_perm _)
  rw [hlen] at h
  change (∫ x in Ω, multiDeriv f α x * ψ x) = _ at h
  rw [h]
  congr 1
  apply setIntegral_congr_fun hΩ.measurableSet
  intro x hx
  exact congrArg (fun y => f x * y) (heq x hx)
