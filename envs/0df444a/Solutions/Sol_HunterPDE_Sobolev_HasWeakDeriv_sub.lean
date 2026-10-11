-- Prove2me | solution 1 for HunterPDE.Sobolev.HasWeakDeriv.sub
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T22:43:05.309787+00:00
-- url     : https://prove2.me/submissions/0ab9029b-9f3d-4065-8510-3e3ac29365fb

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Analysis.MeanInequalities

open MeasureTheory HunterPDE.Sobolev
open scoped ContDiff

namespace HunterPDE.Sobolev

lemma test_mul_integrable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f φ : EuclideanSpace ℝ (Fin n) → ℝ} (hf : LocallyIntegrableOn f Ω)
    (hφ : IsTestFunction Ω φ) : Integrable (fun x => f x * φ x) := by
  apply (integrableOn_iff_integrable_of_support_subset
    (s := tsupport φ) (fun x hx => ?_)).mp
  · exact (hf.integrableOn_compact_subset hφ.2.2 hφ.2.1).mul_continuousOn
      hφ.1.continuous.continuousOn hφ.2.1
  · apply subset_tsupport φ
    simpa only [Function.mem_support] using (mul_ne_zero_iff.mp hx).2

lemma test_partial {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : IsTestFunction Ω φ) (i : Fin n) :
    IsTestFunction Ω (partialDeriv i φ) := by
  refine ⟨?_, hφ.2.1.fderiv_apply ℝ _, (tsupport_fderiv_apply_subset ℝ _).trans hφ.2.2⟩
  exact (hφ.1.contDiff_fderiv_apply (m := ∞) (by simp)).comp
    (contDiff_id.prodMk contDiff_const)

lemma test_iterated {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : IsTestFunction Ω φ) (α : Fin n → ℕ) :
    IsTestFunction Ω (iteratedPartial α φ) := by
  unfold iteratedPartial
  have step (i : Fin n) (m : ℕ) {u : EuclideanSpace ℝ (Fin n) → ℝ}
      (hu : IsTestFunction Ω u) : IsTestFunction Ω ((partialDeriv i)^[m] u) := by
    induction m with
    | zero => simpa using hu
    | succ m ih => simpa only [Function.iterate_succ_apply'] using test_partial ih i
  generalize List.finRange n = l
  induction l with
  | nil => exact hφ
  | cons i l ih => exact step i (α i) ih

end HunterPDE.Sobolev

theorem solution {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {α : Fin n → ℕ} {f g u v : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : HasWeakDeriv Ω α f u) (hv : HasWeakDeriv Ω α g v) :
    HasWeakDeriv Ω α (f - g) (u - v) := by
  refine ⟨hu.1.sub hv.1, hu.2.1.sub hv.2.1, ?_⟩
  intro φ hφ
  simp only [Pi.sub_apply, sub_mul]
  rw [integral_sub (test_mul_integrable hu.2.1 hφ).integrableOn
      (test_mul_integrable hv.2.1 hφ).integrableOn,
    integral_sub (test_mul_integrable hu.1 (test_iterated hφ α)).integrableOn
      (test_mul_integrable hv.1 (test_iterated hφ α)).integrableOn, hu.2.2 φ hφ, hv.2.2 φ hφ,
    mul_sub]

