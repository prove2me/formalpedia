-- Prove2me | solution 1 for HMBinPacking.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:31:07.010307+00:00
-- url     : https://prove2.me/submissions/3ad31e0c-ae7d-4abd-9f26-3c11b27126d9

import Mathlib
open scoped Pointwise

theorem solution {d : ℕ} (V : Set (Fin d → ℝ)) (hVfin : V.Finite) (hVne : V.Nonempty) (t : ℝ)
    (ht : 0 < t) (z : Fin d → ℝ) (hz : z ∈ t • convexHull ℝ V) :
    ∃ (v : Fin (d + 1) → Fin d → ℝ) (α : Fin (d + 1) → ℝ),
      (∀ i, v i ∈ V) ∧ (∀ i, 0 ≤ α i) ∧ z = ∑ i, α i • v i ∧ ∑ i, α i = t := by
  obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hz
  obtain ⟨ι, _, zz, w, hrange, hai, hwpos, hw1, hwz⟩ := eq_pos_convex_span_of_mem_convexHull hy
  have hcard : Fintype.card ι ≤ d + 1 := by
    have h1 := hai.card_le_finrank_succ
    have h2 := Submodule.finrank_le (vectorSpan ℝ (Set.range zz))
    rw [Module.finrank_fin_fun] at h2
    omega
  obtain ⟨n, hn⟩ : ∃ n, n = Fintype.card ι := ⟨_, rfl⟩
  rw [← hn] at hcard
  let e : ι ≃ Fin n := hn ▸ Fintype.equivFin ι
  obtain ⟨v0, hv0⟩ := hVne
  let v : Fin (d + 1) → Fin d → ℝ := fun i =>
    if h : i.val < n then zz (e.symm ⟨i.val, h⟩) else v0
  let α : Fin (d + 1) → ℝ := fun i =>
    if h : i.val < n then t * w (e.symm ⟨i.val, h⟩) else 0
  have hred : ∀ {M : Type} [AddCommMonoid M] (F : Fin (d + 1) → M),
      (∀ i : Fin (d + 1), ¬ i.val < n → F i = 0) →
        ∑ i, F i = ∑ j : Fin n, F (Fin.castLEEmb hcard j) := by
    intro M _ F hF
    rw [← Finset.sum_map Finset.univ (Fin.castLEEmb hcard) F]
    exact (Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => hF x (fun h => hx
      (Finset.mem_map.mpr ⟨⟨x.val, h⟩, Finset.mem_univ _, Fin.ext rfl⟩)))).symm
  have hα' : ∀ j : Fin n, α (Fin.castLEEmb hcard j) = t * w (e.symm j) := by
    intro j
    simp only [α, Fin.coe_castLEEmb, Fin.coe_castLE, dif_pos j.isLt, Fin.eta]
  have hv' : ∀ j : Fin n, v (Fin.castLEEmb hcard j) = zz (e.symm j) := by
    intro j
    simp only [v, Fin.coe_castLEEmb, Fin.coe_castLE, dif_pos j.isLt, Fin.eta]
  refine ⟨v, α, fun i => ?_, fun i => ?_, ?_, ?_⟩
  · simp only [v]
    split_ifs
    · exact hrange ⟨_, rfl⟩
    · exact hv0
  · simp only [α]
    split_ifs
    · exact mul_nonneg ht.le (hwpos _).le
    · exact le_refl 0
  · rw [hred (fun i => α i • v i) (fun i hi => by simp only [α, dif_neg hi, zero_smul])]
    simp only [hα', hv']
    rw [Equiv.sum_comp e.symm (fun a => (t * w a) • zz a), ← hwz, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [mul_smul]
  · rw [hred α (fun i hi => by simp only [α, dif_neg hi])]
    simp only [hα']
    rw [Equiv.sum_comp e.symm (fun a => t * w a), ← Finset.mul_sum, hw1, mul_one]
