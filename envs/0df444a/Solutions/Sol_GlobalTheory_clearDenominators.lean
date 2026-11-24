-- Prove2me | solution 1 for GlobalTheory.clearDenominators
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:29:11.859487+00:00
-- url     : https://prove2.me/submissions/85538e87-64cc-4dac-b1a9-442003da3adc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_MvPolynomialClearDenominatorsEval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial Finset
namespace GlobalTheory
theorem _root_.solution {K : Type} [Field K] {ι τ : Type} (F : MvPolynomial ι K)
    (P D : ι → MvPolynomial τ K) :
    ∃ G M : MvPolynomial τ K, ∀ y : τ → K, (∀ i, MvPolynomial.eval y (D i) ≠ 0) →
      MvPolynomial.eval y M ≠ 0 ∧
      MvPolynomial.eval y G = MvPolynomial.eval y M *
        MvPolynomial.eval (fun i => MvPolynomial.eval y (P i) / MvPolynomial.eval y (D i)) F := by
  classical
  set N := F.totalDegree
  refine ⟨∑ m ∈ F.support, C (F.coeff m) * ∏ i ∈ F.vars, (P i) ^ (m i) * (D i) ^ (N - m i),
    ∏ i ∈ F.vars, (D i) ^ N, fun y hy => ⟨?_, ?_⟩⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => by rw [map_pow]; exact pow_ne_zero _ (hy i)
  · have hle : ∀ m ∈ F.support, ∀ i, m i ≤ N := fun m hm i =>
      (monomial_le_degreeOf i hm).trans (degreeOf_le_totalDegree F i)
    have hsub : ∀ m ∈ F.support, m.support ⊆ F.vars := fun m hm i hi =>
      (mem_vars i).mpr ⟨m, hm, hi⟩
    rw [MvPolynomial.eval_eq (fun i => MvPolynomial.eval y (P i) / MvPolynomial.eval y (D i)) F,
      map_prod, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [map_mul, eval_C, map_prod]
    rw [Finset.prod_subset (hsub m hm) (fun i _ hi => by
      rw [Finsupp.notMem_support_iff.mp hi, pow_zero])]
    rw [mul_left_comm, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [map_mul, map_pow]
    have hd := hy i
    have hk := hle m hm i
    rw [div_pow, ← pow_sub_mul_pow (MvPolynomial.eval y (D i)) hk]
    field_simp
end GlobalTheory
