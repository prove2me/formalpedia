-- Prove2me | solution 1 for KernelRank.span_expMonomial_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:38:39.08623+00:00
-- url     : https://prove2.me/submissions/26b71554-b775-4771-b638-576b1ddc7a63

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_MultiComplexRank
import Theorems.Thm_KernelRank_span_range_eq_top_of_dual
import Theorems.Thm_KernelRank_singleCoeff_same
import Theorems.Thm_KernelRank_singleCoeff_of_ne_idx
import Theorems.Thm_KernelRank_singleCoeff_of_ne_deg
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
import Theorems.Thm_P2M_KernelRank_eq_zero_of_sum_expPoly_eq_zero__c58c8e720b46
attribute [local simp] KernelRank.expPoly_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero


attribute [local simp] KernelRank.singleCoeff_same

set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank
namespace KernelRank
theorem _root_.solution {ι : Type*} [Finite ι] {rate : ι → ℂ}
    (hinj : Function.Injective rate) (m₀ : ι → ℕ) :
    Submodule.span ℂ
      (Set.range fun s : ℝ≥0 => fun (i : ι) (q : Fin (m₀ i)) =>
        ((s : ℂ) ^ (q : ℕ) / ((q : ℕ).factorial : ℂ)) * exp (rate i * (s : ℂ))) = ⊤ := by
  cases nonempty_fintype ι
  classical
  refine span_range_eq_top_of_dual fun L hL => ?_
  let a (i : ι) (q : Fin (m₀ i)) : ℂ := L (singleCoeff i q 1)
  have hL_expand (x : ∀ i, Fin (m₀ i) → ℂ) :
      L x = ∑ i : ι, ∑ q : Fin (m₀ i), a i q * x i q := by
    have hx : x = ∑ i : ι, ∑ q : Fin (m₀ i), x i q • singleCoeff i q 1 := by
      ext i₀ q₀
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single i₀]
      · rw [Finset.sum_eq_single q₀]
        · simp
        · intro q _ hq
          simp [singleCoeff_of_ne_deg i₀ q q₀ 1 hq.symm]
        · simp
      · intro i _ hi
        exact Finset.sum_eq_zero fun q _ => by simp [singleCoeff_of_ne_idx i q 1 hi.symm]
      · simp
    conv_lhs => rw [hx]
    simp [map_sum, map_smul, a, mul_comm]
  let Q (i : ι) : ℂ[X] :=
    ∑ q : Fin (m₀ i), C (a i q / ((q : ℕ).factorial : ℂ)) * X ^ (q : ℕ)
  have hQ0 : ∀ i, Q i = 0 := by
    refine eq_zero_of_sum_expPoly_eq_zero' hinj Q fun u hu => ?_
    have hs := hL ⟨u, hu.le⟩
    rw [hL_expand] at hs
    rw [← hs]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Q, expPoly, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    change (a i q / ((q : ℕ).factorial : ℂ)) * (u : ℂ) ^ (q : ℕ) * exp (rate i * (u : ℂ)) =
      a i q * (((u : ℂ) ^ (q : ℕ) / ((q : ℕ).factorial : ℂ)) * exp (rate i * (u : ℂ)))
    ring
  have ha0 (i : ι) (q : Fin (m₀ i)) : a i q = 0 := by
    have hc := congrArg (fun p => p.coeff (q : ℕ)) (hQ0 i)
    simp only [Q, finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at hc
    rw [Finset.sum_eq_single q] at hc
    · simp only [↓reduceIte, mul_one] at hc
      have hfq : ((q : ℕ).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (q : ℕ).factorial_ne_zero
      exact (div_eq_zero_iff.mp hc).resolve_right hfq
    · intro q' _ hne
      have : (q : ℕ) ≠ (q' : ℕ) := fun h => hne (Fin.ext h.symm)
      simp [this]
    · simp
  ext x
  simp [hL_expand, ha0]
end KernelRank
