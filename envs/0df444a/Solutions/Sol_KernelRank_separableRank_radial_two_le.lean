-- Prove2me | solution 1 for KernelRank.separableRank_radial_two_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:56:39.307601+00:00
-- url     : https://prove2.me/submissions/a4befdc0-87fe-4960-8164-f57c8bd35b79

import Definitions.Def_KernelRankLean_RowSpan
import Definitions.Def_KernelRankLean_Translations
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
import Theorems.Thm_KernelRank_separableRank_padTwo_le
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero



set_option autoImplicit true
open NNReal
open KernelRank
namespace KernelRank
theorem _root_.solution {𝕜 : Type*} [CommSemiring 𝕜] {d : ℕ} (hd : 2 ≤ d)
    (φ : ℝ → 𝕜) :
    separableRank (fun y : Fin 2 → ℝ => φ (∑ k, y k ^ 2)) ≤
      separableRank (fun x : Fin d → ℝ => φ (∑ i, x i ^ 2)) := by
  have hpad : (fun y : Fin 2 → ℝ => φ (∑ i : Fin d, padTwo y i ^ 2)) =
      fun y : Fin 2 → ℝ => φ (∑ k : Fin 2, y k ^ 2) := by
    funext y
    congr 1
    have hsplit := (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin d => (i : ℕ) < 2) (fun i => padTwo y i ^ 2)).symm
    have hrest : ∑ i ∈ Finset.univ.filter (fun i : Fin d => ¬ (i : ℕ) < 2),
        padTwo y i ^ 2 = 0 :=
      Finset.sum_eq_zero fun i hi => by
        have hi' : ¬ (i : ℕ) < 2 := (Finset.mem_filter.mp hi).2
        simp [padTwo, hi']
    have htwo : ∑ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) < 2), padTwo y i ^ 2 =
        y 0 ^ 2 + y 1 ^ 2 := by
      have hset : Finset.univ.filter (fun i : Fin d => (i : ℕ) < 2) =
          {Fin.castLE hd 0, Fin.castLE hd 1} := by
        ext ⟨i, hi⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, Fin.ext_iff, Fin.val_castLE, Fin.val_zero, Fin.val_one]
        omega
      have hne : Fin.castLE hd 0 ≠ Fin.castLE hd 1 := by simp [Fin.ext_iff]
      rw [hset, Finset.sum_pair hne]
      simp [padTwo, Fin.castLE]
    rw [hsplit, hrest, add_zero, htwo, Fin.sum_univ_two]
  have h := separableRank_padTwo_le hd (fun x : Fin d → ℝ => φ (∑ i, x i ^ 2))
  rwa [hpad] at h
end KernelRank
