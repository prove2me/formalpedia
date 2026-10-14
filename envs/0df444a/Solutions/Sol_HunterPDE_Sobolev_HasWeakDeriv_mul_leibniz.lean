-- Prove2me | solution 1 for HunterPDE.Sobolev.HasWeakDeriv.mul_leibniz
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-11T22:19:43.012007+00:00
-- url     : https://prove2.me/submissions/531bddb8-cd87-4547-8d2e-7dc617039830

import Theorems.Thm_HunterPDE_Sobolev_iteratedPartial_adjoint_leibniz
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Tactic.Ring

open MeasureTheory HunterPDE.Sobolev
open scoped ContDiff

namespace MulLeibnizProof

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


lemma smooth_iterated {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) (α : Fin n → ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (iteratedPartial α u) := by
  unfold iteratedPartial
  have step (i : Fin n) (m : ℕ) {v : EuclideanSpace ℝ (Fin n) → ℝ}
      (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v) :
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ((partialDeriv i)^[m] v) := by
    induction m with
    | zero => simpa using hv
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact (ih.contDiff_fderiv_apply (m := ∞) (by simp)).comp
          (contDiff_id.prodMk contDiff_const)
  generalize List.finRange n = l
  induction l with
  | nil => exact hu
  | cons i l ih => exact step i (α i) ih

lemma test_smooth_mul {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) (hφ : IsTestFunction Ω φ) :
    IsTestFunction Ω (fun x => u x * φ x) :=
  ⟨hu.mul hφ.1, hφ.2.1.mul_left, tsupport_mul_subset_right.trans hφ.2.2⟩

end MulLeibnizProof

open MulLeibnizProof

theorem solution {n k : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (f η : EuclideanSpace ℝ (Fin n) → ℝ)
    (d : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℝ)
    (hd : ∀ β, ∑ i, β i ≤ k → HasWeakDeriv Ω β f (d β))
    (hη : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η)
    (α : Fin n → ℕ) (hα : ∑ i, α i ≤ k) :
    HasWeakDeriv Ω α (fun x => η x * f x)
      (fun x => ∑ β ∈ multiIndices n k,
        (∏ i, (Nat.choose (α i) (β i) : ℝ)) *
          iteratedPartial (fun i => α i - β i) η x * d β x) := by
  classical
  let c : (Fin n → ℕ) → ℝ := fun β => ∏ i, (Nat.choose (α i) (β i) : ℝ)
  let u : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun β => iteratedPartial (fun i => α i - β i) η
  have hu (β : Fin n → ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u β) :=
    smooth_iterated hη _
  have order (β : Fin n → ℕ) (hβ : β ∈ multiIndices n k) : ∑ i, β i ≤ k :=
    (Finset.mem_filter.mp hβ).2
  have hf : LocallyIntegrableOn f Ω := (hd α hα).1
  have hg (β : Fin n → ℕ) (hβ : β ∈ multiIndices n k) :
      LocallyIntegrableOn (fun x => c β * u β x * d β x) Ω :=
    (hd β (order β hβ)).2.1.continuousOn_mul
      (continuous_const.mul (hu β).continuous).continuousOn hΩ.isLocallyClosed
  refine ⟨hf.continuousOn_mul hη.continuous.continuousOn hΩ.isLocallyClosed, ?_, ?_⟩
  · rw [locallyIntegrableOn_iff hΩ.isLocallyClosed]
    intro K hK hKc
    exact integrable_finsetSum _ (fun β hβ =>
      (hg β hβ).integrableOn_compact_subset hK hKc)
  · intro φ hφ
    have ht (β : Fin n → ℕ) : IsTestFunction Ω (fun x => u β x * φ x) :=
      test_smooth_mul (hu β) hφ
    have hi (β : Fin n → ℕ) (hβ : β ∈ multiIndices n k) :
        IntegrableOn (fun x => c β * u β x * d β x * φ x) Ω :=
      (test_mul_integrable (hg β hβ) hφ).integrableOn
    have hj (β : Fin n → ℕ) :
        IntegrableOn (fun x => f x * iteratedPartial β (fun y => u β y * φ y) x) Ω :=
      (test_mul_integrable hf (test_iterated (ht β) β)).integrableOn
    calc
      _ = ∑ β ∈ multiIndices n k, ∫ x in Ω, c β * u β x * d β x * φ x := by
        simp only [Finset.sum_mul]
        exact integral_finsetSum _ hi
      _ = ∑ β ∈ multiIndices n k, c β * (-1 : ℝ) ^ (∑ i, β i) *
          ∫ x in Ω, f x * iteratedPartial β (fun y => u β y * φ y) x := by
        apply Finset.sum_congr rfl
        intro β hβ
        have he : (fun x => c β * u β x * d β x * φ x) =
            (fun x => c β * (d β x * (u β x * φ x))) := by funext x; ring
        rw [he, integral_const_mul, (hd β (order β hβ)).2.2 _ (ht β)]
        ring
      _ = ∫ x in Ω, f x * (∑ β ∈ multiIndices n k,
          c β * (-1 : ℝ) ^ (∑ i, β i) *
            iteratedPartial β (fun y => u β y * φ y) x) := by
        simp only [Finset.mul_sum]
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro β hβ
          rw [show (fun x => f x * (c β * (-1 : ℝ) ^ (∑ i, β i) *
              iteratedPartial β (fun y => u β y * φ y) x)) =
              (fun x => (c β * (-1 : ℝ) ^ (∑ i, β i)) *
                (f x * iteratedPartial β (fun y => u β y * φ y) x)) by funext x; ring]
          rw [integral_const_mul]
        · intro β hβ
          convert (hj β).const_mul (c β * (-1 : ℝ) ^ (∑ i, β i)) using 1 <;>
            ext x <;> ring
      _ = (-1 : ℝ) ^ (∑ i, α i) * ∫ x in Ω, (η x * f x) * iteratedPartial α φ x := by
        simp only [c, u, iteratedPartial_adjoint_leibniz η φ hη hφ.1 α hα]
        rw [show (fun x => f x * ((-1 : ℝ) ^ (∑ i, α i) * η x * iteratedPartial α φ x)) =
            (fun x => (-1 : ℝ) ^ (∑ i, α i) * ((η x * f x) * iteratedPartial α φ x)) by
              funext x; ring, integral_const_mul]
