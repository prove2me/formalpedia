-- Prove2me | solution 1 for GlobalTheory.PrimeDivisorOfPolynomialValue.exists_eval_mul_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:29:31.118393+00:00
-- url     : https://prove2.me/submissions/c22c83d1-d360-4752-a6a6-cd6ea7961e38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimeGtDvdEval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PrimeDivisorOfPolynomialValue
open Polynomial
namespace GlobalTheory.PrimeDivisorOfPolynomialValue
theorem _root_.solution (f : ℤ[X]) (hf : 0 < f.natDegree) (c a : ℤ) (ha : a ≠ 0) :
    ∃ k : ℤ, f.eval (a * k) ≠ c ∧ f.eval (a * k) ≠ -c := by

  have hdeg : 0 < (f.comp (C a * X)).natDegree := by
    rw [natDegree_comp, natDegree_C_mul_X a ha, mul_one]
    exact hf
  have hne : ∀ b : ℤ, f.comp (C a * X) - C b ≠ 0 := fun b h => by
    rw [sub_eq_zero] at h
    rw [h, natDegree_C] at hdeg
    exact lt_irrefl 0 hdeg
  obtain ⟨k, hk⟩ := Infinite.exists_notMem_finset
    ((f.comp (C a * X) - C c).roots.toFinset ∪ (f.comp (C a * X) - C (-c)).roots.toFinset)
  refine ⟨k, fun e => hk (Finset.mem_union_left _ ?_), fun e => hk (Finset.mem_union_right _ ?_)⟩
  · rw [Multiset.mem_toFinset, mem_roots (hne c)]
    simp [e]
  · rw [Multiset.mem_toFinset, mem_roots (hne (-c))]
    simp [e]
end GlobalTheory.PrimeDivisorOfPolynomialValue
