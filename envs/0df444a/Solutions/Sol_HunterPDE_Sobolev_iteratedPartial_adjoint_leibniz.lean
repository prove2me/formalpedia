-- Prove2me | solution 1 for HunterPDE.Sobolev.iteratedPartial_adjoint_leibniz
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T14:38:38.435977+00:00
-- url     : https://prove2.me/submissions/9addefcc-12e0-447a-8a84-473a2460abaa

import Theorems.Thm_HunterPDE_Sobolev_iteratedPartial_shifted_mul
import Theorems.Thm_MultiIndex_alternating_binomial_convolution

open HunterPDE.Sobolev

theorem solution {n k : ℕ}
    (η φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hη : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (α : Fin n → ℕ) (hα : ∑ i, α i ≤ k) (x : EuclideanSpace ℝ (Fin n)) :
    (∑ β ∈ multiIndices n k,
      (∏ i, (Nat.choose (α i) (β i) : ℝ)) * (-1 : ℝ) ^ (∑ i, β i) *
        iteratedPartial β (fun y => iteratedPartial (fun i => α i - β i) η y * φ y) x) =
      (-1 : ℝ) ^ (∑ i, α i) * η x * iteratedPartial α φ x := by
  classical
  have hmem (β : Fin n → ℕ) (hβ : ∑ i, β i ≤ k) : β ∈ multiIndices n k := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, hβ⟩
    apply Finset.mem_image.mpr
    let b : Fin n → Fin (k + 1) := fun i =>
      ⟨β i, Nat.lt_succ_of_le ((Finset.single_le_sum (fun j _ => Nat.zero_le (β j))
        (Finset.mem_univ i)).trans hβ)⟩
    exact ⟨b, Finset.mem_univ _, rfl⟩
  have hcover : ∀ β : Fin n → ℕ, (∀ i, β i ≤ α i) → β ∈ multiIndices n k := by
    intro β hβ
    exact hmem β ((Finset.sum_le_sum (fun i _ => hβ i)).trans hα)
  have hexpand (β : Fin n → ℕ) (hβ : β ∈ multiIndices n k) :
      iteratedPartial β (fun y => iteratedPartial (fun i => α i - β i) η y * φ y) x =
        ∑ γ ∈ multiIndices n k, (∏ i, (Nat.choose (β i) (γ i) : ℝ)) *
          (iteratedPartial (fun i => α i - β i + (β i - γ i)) η x *
            iteratedPartial γ φ x) := by
    apply iteratedPartial_shifted_mul η φ hη hφ
    intro γ hγ
    exact hmem γ ((Finset.sum_le_sum (fun i _ => hγ i)).trans
      (Finset.mem_filter.mp hβ).2)
  have hzero : iteratedPartial (fun _ : Fin n => 0) η = η := by
    simp only [iteratedPartial, Function.iterate_zero, id_eq]
    induction List.finRange n with
    | nil => rfl
    | cons i l ih => simpa only [List.foldr_cons, id_eq] using ih
  calc
    _ = ∑ β ∈ multiIndices n k,
        (∏ i, (Nat.choose (α i) (β i) : ℝ)) * (-1 : ℝ) ^ (∑ i, β i) *
          (∑ γ ∈ multiIndices n k, (∏ i, (Nat.choose (β i) (γ i) : ℝ)) *
            (iteratedPartial (fun i => α i - β i + (β i - γ i)) η x *
              iteratedPartial γ φ x)) := by
      apply Finset.sum_congr rfl
      intro β hβ
      rw [hexpand β hβ]
    _ = (-1 : ℝ) ^ (∑ i, α i) *
        (iteratedPartial (fun _ => 0) η x * iteratedPartial α φ x) :=
      MultiIndex.alternating_binomial_convolution α (multiIndices n k) hcover
        (fun δ γ => iteratedPartial δ η x * iteratedPartial γ φ x)
    _ = _ := by rw [hzero]; ring
