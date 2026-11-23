-- Prove2me | solution 1 for KernelRank.differentialOperator_sum_expPoly_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:41:07.353626+00:00
-- url     : https://prove2.me/submissions/d2f23501-ce7d-4e3d-b222-5dfe9c324c0a

import Definitions.Def_KernelRankLean_Differential
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_ComplexRank
import Theorems.Thm_KernelRank_aeval_shifted_derivative_eq_zero_iff
import Theorems.Thm_KernelRank_differentialOperator_sum_expPoly
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_P2M_KernelRank_eq_zero_of_sum_expPoly_eq_zero__c58c8e720b46
attribute [local simp] KernelRank.expPoly_zero



set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank
namespace KernelRank
theorem _root_.solution {ι : Type*} [Fintype ι]
    (P : ι → ℂ[X]) (rate : ι → ℂ) (hinj : Function.Injective rate)
    (hP : ∀ i, P i ≠ 0) (q : ℂ[X]) :
    (∀ t, 0 ≤ t → differentialOperator q (fun u => ∑ i, expPoly (P i) (rate i) u) t = 0) ↔
      expPolyAnnihilator P rate ∣ q := by
  constructor
  · intro h
    change (∏ i, (X - C (rate i)) ^ ((P i).natDegree + 1)) ∣ q
    apply Fintype.prod_dvd_of_coprime
      (fun i j hij => (pairwise_coprime_X_sub_C hinj hij).pow)
    intro i
    apply (aeval_shifted_derivative_eq_zero_iff q (hP i) (rate i)).mp
    exact eq_zero_of_sum_expPoly_eq_zero' hinj _ (fun t ht => by
      rw [← differentialOperator_sum_expPoly q P rate ht.le]
      exact h t ht.le) i
  · intro h t ht
    rw [differentialOperator_sum_expPoly q P rate ht]
    apply Finset.sum_eq_zero
    intro i _
    have hi' : (X - C (rate i)) ^ ((P i).natDegree + 1) ∣ expPolyAnnihilator P rate :=
      Finset.dvd_prod_of_mem
        (fun j : ι => (X - C (rate j)) ^ ((P j).natDegree + 1)) (Finset.mem_univ i)
    have hi := dvd_trans hi' h
    rw [(aeval_shifted_derivative_eq_zero_iff q (hP i) (rate i)).mpr hi, expPoly_zero]
end KernelRank
