-- Prove2me | solution 1 for KernelRank.separableRank_sum_expPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:43:25.231867+00:00
-- url     : https://prove2.me/submissions/fb0ad07c-a790-4c4d-8514-9245441c04f6

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_MultiComplexRank
import Theorems.Thm_KernelRank_isSumOfProducts_expPoly
import Theorems.Thm_KernelRank_exists_linear_factors_of_span_eq_top
import Theorems.Thm_KernelRank_singleCoeff_same
import Theorems.Thm_KernelRank_truncForm_rank_ge
import Theorems.Thm_KernelRank_sum_expPoly_eq_truncForm
import Theorems.Thm_KernelRank_truncMultilinearMap_apply
import Theorems.Thm_KernelRank_span_expMonomial_eq_top
import Theorems.Thm_KernelRank_IsSumOfProducts_finsetSum
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
attribute [local simp] KernelRank.expPoly_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero


attribute [local simp] KernelRank.singleCoeff_same

set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank
namespace KernelRank
theorem _root_.solution {d : ℕ} (hd : 2 ≤ d) {ι : Type*} [Fintype ι] {rate : ι → ℂ}
    (hinj : Function.Injective rate) (P : ι → ℂ[X]) (hP : ∀ i, P i ≠ 0) :
    separableRank (fun s : Fin d → ℝ≥0 => ∑ i, expPoly (P i) (rate i) (∑ j, (s j : ℝ))) =
      (∑ i, ((d - 1) * (P i).natDegree + 1) : ℕ) := by
  classical
  refine le_antisymm ?_ ?_
  · exact iInf₂_le _ (IsSumOfProducts.finsetSum fun i =>
      isSumOfProducts_expPoly hd (P i) (rate i))
  · refine le_iInf₂ fun R hR => ?_
    let m₀ (i : ι) : ℕ := (P i).natDegree + 1
    let w (i : ι) (k : ℕ) : ℂ := (k.factorial : ℂ) * (P i).coeff k
    let v (s : ℝ≥0) (i : ι) (q : Fin (m₀ i)) : ℂ :=
      ((s : ℂ) ^ (q : ℕ) / ((q : ℕ).factorial : ℂ)) * exp (rate i * (s : ℂ))
    have hK_eq : (fun s : Fin d → ℝ≥0 => ∑ i, expPoly (P i) (rate i) (∑ j, (s j : ℝ))) =
        fun s => truncMultilinearMap d m₀ m₀ w (fun j => v (s j)) := by
      funext s
      rw [truncMultilinearMap_apply, sum_expPoly_eq_truncForm]
    rw [hK_eq] at hR
    obtain ⟨ℓ, hℓ⟩ := exists_linear_factors_of_span_eq_top (span_expMonomial_eq_top hinj m₀)
      (truncMultilinearMap d m₀ m₀ w) hR
    simp_rw [truncMultilinearMap_apply] at hℓ
    have hw : ∀ i, 0 < m₀ i → w i (m₀ i - 1) ≠ 0 := fun i _ => by
      dsimp [w, m₀]
      exact mul_ne_zero (Nat.cast_ne_zero.mpr (P i).natDegree.factorial_ne_zero)
        (leadingCoeff_ne_zero.mpr (hP i))
    have hge := truncForm_rank_ge hd m₀ (∑ i, m₀ i) m₀ rfl (fun _ => le_rfl) w hw R ℓ hℓ
    have hsum : (∑ i, if m₀ i = 0 then 0 else (d - 1) * (m₀ i - 1) + 1) =
        ∑ i, ((d - 1) * (P i).natDegree + 1) :=
      Finset.sum_congr rfl fun i _ => by simp [m₀]
    rw [hsum] at hge
    exact_mod_cast hge
end KernelRank
