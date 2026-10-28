-- Prove2me | solution 1 for KKM.exists_mem_convexHull_mem_iInter
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T04:08:14.450172+00:00
-- url     : https://prove2.me/submissions/bd76e73c-54e7-4f1b-9fb0-681300eb0517

import Mathlib
import Theorems.Thm_KKM_exists_mem_iInter_stdSimplex

-- carved verbatim out of submission 818ed08f-1f44-45cc-90a9-3239f8bb6e07, lines 869-912

section

theorem solution {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (n : ℕ) (a : Fin (n + 1) → E)
    (A : Fin (n + 1) → Set E)
    (hA : ∀ i, IsOpen (A i))
    (hcov : convexHull ℝ (Set.range a) ⊆ ⋃ i, A i)
    (hconv : ∀ i, Convex ℝ (convexHull ℝ (Set.range a) \ A i))
    (hv : ∀ i j, i ≠ j → a i ∉ A j) :
    ∃ z ∈ convexHull ℝ (Set.range a), ∀ i, z ∈ A i := by
  classical
  let ψ : (Fin (n+1) → ℝ) →ₗ[ℝ] E := Fintype.linearCombination ℝ a
  have hψ : ∀ x, ψ x = ∑ i, x i • a i := fun x => by
    simp [ψ, Fintype.linearCombination_apply]
  have hψc : Continuous ψ := by
    have : (ψ : (Fin (n+1) → ℝ) → E) = fun x => ∑ i, x i • a i := funext hψ
    rw [this]
    exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
  have hψS : ∀ x ∈ stdSimplex ℝ (Fin (n+1)), ψ x ∈ convexHull ℝ (Set.range a) := by
    intro x hx
    rw [hψ]
    exact (convex_convexHull ℝ _).sum_mem (fun i _ => hx.1 i) hx.2
      (fun i _ => subset_convexHull ℝ _ (Set.mem_range_self i))
  obtain ⟨x, hx, hxA⟩ := KKM.exists_mem_iInter_stdSimplex n (fun i => ψ ⁻¹' A i) (fun i => (hA i).preimage hψc)
    (fun x hx => by
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov (hψS x hx))
      exact ⟨i, hi⟩)
    (fun i => by
      have : stdSimplex ℝ (Fin (n+1)) \ ψ ⁻¹' A i
          = stdSimplex ℝ (Fin (n+1)) ∩ (ψ ⁻¹' (convexHull ℝ (Set.range a) \ A i)) := by
        ext x
        simp only [Set.mem_diff, Set.mem_inter_iff, Set.mem_preimage]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1, hψS x h1, h2⟩
        · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
      rw [this]
      exact (convex_stdSimplex ℝ (Fin (n+1))).inter ((hconv i).linear_preimage ψ))
    (fun i j hij => by
      have : ψ (Pi.single i 1) = a i := by
        rw [hψ]
        simp [Pi.single_apply]
      simp only [Set.mem_preimage, this]
      exact hv i j hij)
  exact ⟨ψ x, hψS x hx, fun i => hxA i⟩

end
