-- Prove2me | solution 1 for KernelRank.single_complex_rank_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:38:30.82278+00:00
-- url     : https://prove2.me/submissions/a751dc0e-f3f1-4bc0-b307-49ab37de0276

import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_MultiRealRank
import Theorems.Thm_KernelRank_exists_ker_ne_zero
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
import Theorems.Thm_KernelRank_singleCoeff_same
attribute [local simp] KernelRank.expPoly_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero
attribute [local simp] KernelRank.singleCoeff_same



set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank
namespace KernelRank
theorem _root_.solution {d : ℕ} (hd : 2 ≤ d) :
    ∀ {β : ℂ}, β ≠ 0 → ∀ {R : ℕ} (ℓ : Fin R → Fin d → (ℂ →ₗ[ℝ] ℝ)),
      (∀ z : Fin d → ℂ, (β * ∏ j, z j).re = ∑ n, ∏ j, ℓ n j (z j)) → d ≤ R := by
  induction d, hd using Nat.le_induction with
  | base =>
    intro β hβ R ℓ hrepr
    by_contra hlt
    rcases (show R = 0 ∨ R = 1 by omega) with rfl | rfl
    · have h := hrepr (fin2Vec 1 (starRingEnd ℂ β))
      simp only [Fin.prod_univ_two, fin2Vec_zero, fin2Vec_one, one_mul, Finset.univ_eq_empty,
        Finset.sum_empty] at h
      rw [Complex.mul_conj, Complex.ofReal_re] at h
      exact (Complex.normSq_pos.mpr hβ).ne' h
    · obtain ⟨w, hw0, hw_ker⟩ := exists_ker_ne_zero (ℓ 0 0)
      have h := hrepr (fin2Vec w (starRingEnd ℂ (β * w)))
      simp only [Fin.prod_univ_two, fin2Vec_zero, fin2Vec_one, Finset.univ_unique,
        Fin.default_eq_zero, Finset.sum_singleton, hw_ker, zero_mul] at h
      rw [← mul_assoc, Complex.mul_conj, Complex.ofReal_re] at h
      exact (Complex.normSq_pos.mpr (mul_ne_zero hβ hw0)).ne' h
  | succ d hd ih =>
    intro β hβ R ℓ hrepr
    cases R with
    | zero =>
      exfalso
      let z (j : Fin (d + 1)) : ℂ := if j = 0 then starRingEnd ℂ β else 1
      have hprod : ∏ j : Fin (d + 1), z j = starRingEnd ℂ β := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (0 : Fin (d + 1)))]
        have her : ∏ j ∈ Finset.univ.erase (0 : Fin (d + 1)), z j = 1 :=
          Finset.prod_eq_one fun j hj => by simp [z, Finset.ne_of_mem_erase hj]
        simp [z, her]
      have h := hrepr z
      simp only [hprod, Finset.univ_eq_empty, Finset.sum_empty, Complex.mul_conj,
        Complex.ofReal_re] at h
      exact (Complex.normSq_pos.mpr hβ).ne' h
    | succ R =>
      obtain ⟨w, hw0, hw_ker⟩ := exists_ker_ne_zero (ℓ (Fin.last R) (Fin.last d))
      have hd0 : 0 < d := by omega
      let j₀ : Fin d := ⟨0, hd0⟩
      let ℓ' (n : Fin R) (j : Fin d) : ℂ →ₗ[ℝ] ℝ :=
        if j = j₀ then (ℓ n.castSucc (Fin.last d) w) • ℓ n.castSucc j.castSucc
        else ℓ n.castSucc j.castSucc
      have hrepr' (z : Fin d → ℂ) :
          ((β * w) * ∏ j, z j).re = ∑ n : Fin R, ∏ j, ℓ' n j (z j) := by
        have h := hrepr (Fin.snoc (α := fun _ => ℂ) z w)
        rw [Fin.prod_univ_castSucc] at h
        simp only [Fin.snoc_castSucc, Fin.snoc_last] at h
        have hbw : β * ((∏ j, z j) * w) = (β * w) * ∏ j, z j := by ring
        rw [hbw, Fin.sum_univ_castSucc] at h
        have hlast : (∏ j : Fin (d + 1),
            ℓ (Fin.last R) j (Fin.snoc (α := fun _ => ℂ) z w j)) = 0 := by
          rw [Fin.prod_univ_castSucc, Fin.snoc_last, hw_ker, mul_zero]
        rw [hlast, add_zero] at h
        rw [h]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Fin.prod_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        rw [← Finset.mul_prod_erase Finset.univ (fun j => ℓ' n j (z j)) (Finset.mem_univ j₀),
          ← Finset.mul_prod_erase Finset.univ (fun j => ℓ n.castSucc j.castSucc (z j))
            (Finset.mem_univ j₀)]
        have her : ∏ j ∈ Finset.univ.erase j₀, ℓ' n j (z j) =
            ∏ j ∈ Finset.univ.erase j₀, ℓ n.castSucc j.castSucc (z j) :=
          Finset.prod_congr rfl fun j hj => by
            simp [ℓ', Finset.ne_of_mem_erase hj]
        rw [her]
        have hj₀ : ℓ' n j₀ (z j₀) =
            ℓ n.castSucc (Fin.last d) w * ℓ n.castSucc j₀.castSucc (z j₀) := by
          simp [ℓ']
        rw [hj₀]
        ring
      have hle := ih (mul_ne_zero hβ hw0) ℓ' hrepr'
      omega
end KernelRank
