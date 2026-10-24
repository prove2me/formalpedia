-- Prove2me | solution 1 for HiringLP.Parallel.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T17:19:12.670277+00:00
-- url     : https://prove2.me/submissions/2d55746a-ab13-4830-8895-d90f6e2db93b

import Mathlib
import Definitions.Def_HiringLP_Parallel_Model

open HiringLP.Parallel Finset

theorem solution {n k : ℕ} (I : Instance n k) (hI : I.Valid) (q w : Fin n → ℝ)
    (hp : ∀ i j, I.p i j = q i) (hv : ∀ i j, I.v i j = w i) :
    LPpar I = LPseq (seqOfIdentical I q w) := by
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast hI.1
  have hk0 : (0 : ℝ) < k := by linarith
  unfold LPpar LPseq
  congr 1
  ext r
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨fun i => ∑ j, z i j, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · show ∑ i, ∑ j, z i j ≤ ((k * I.T : ℕ) : ℝ)
        rw [Finset.sum_comm]
        calc ∑ j, ∑ i, z i j ≤ ∑ _j : Fin k, (I.T : ℝ) := Finset.sum_le_sum (fun j _ => hz.1 j)
          _ = _ := by simp
      · show ∑ i, (∑ j, z i j) * q i ≤ (k : ℝ)
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        calc ∑ j, ∑ i, z i j * q i ≤ ∑ _j : Fin k, (1 : ℝ) := by
              refine Finset.sum_le_sum (fun j _ => ?_)
              have := hz.2.1 j
              simp only [hp] at this; exact this
          _ = _ := by simp
      · intro i
        exact ⟨Finset.sum_nonneg (fun j _ => (hz.2.2.2 i j).1), hz.2.2.1 i⟩
    · show ∑ i, w i * (∑ j, z i j) * q i = ∑ j, ∑ i, I.v i j * z i j * I.p i j
      simp only [hp, hv]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum, Finset.sum_mul]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨fun i _ => y i / k, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_⟩
      · intro j
        have h := hy.1
        show ∑ i, y i / k ≤ (I.T : ℝ)
        rw [← Finset.sum_div, div_le_iff₀ hk0]
        have : ((k * I.T : ℕ) : ℝ) = (I.T : ℝ) * k := by push_cast; ring
        change ∑ i, y i ≤ ((k * I.T : ℕ) : ℝ) at h
        linarith
      · intro j
        have h := hy.2.1
        change ∑ i, y i * q i ≤ (k : ℝ) at h
        simp only [hp]
        have : ∑ i, y i / k * q i = (∑ i, y i * q i) / k := by
          rw [Finset.sum_div]; refine Finset.sum_congr rfl (fun i _ => ?_); ring
        rw [this, div_le_iff₀ hk0]; linarith
      · intro i
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [mul_div_cancel₀ _ hk0.ne']
        exact (hy.2.2 i).2
      · intro i j
        refine ⟨div_nonneg (hy.2.2 i).1 hk0.le, ?_⟩
        rw [div_le_iff₀ hk0]; nlinarith [(hy.2.2 i).2, (hy.2.2 i).1]
    · show ∑ j, ∑ i, I.v i j * (y i / k) * I.p i j = ∑ i, w i * y i * q i
      simp only [hp, hv]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
