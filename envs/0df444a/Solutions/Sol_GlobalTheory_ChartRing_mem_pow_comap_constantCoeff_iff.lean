-- Prove2me | solution 1 for GlobalTheory.ChartRing.mem_pow_comap_constantCoeff_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:57:43.37426+00:00
-- url     : https://prove2.me/submissions/d580cd56-acf6-423d-a7d3-39f3906fdda6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsAdicCompleteComapConstantCoeff
import Theorems.Thm_GlobalTheory_ChartRing_evalAdic_X
import Theorems.Thm_GlobalTheory_ChartRing_evalAdic_C
import Theorems.Thm_GlobalTheory_ChartRing_map_C_sup_span_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.ChartRing.evalAdic_X
attribute [local simp] GlobalTheory.ChartRing.evalAdic_C

set_option autoImplicit false
open PowerSeries
noncomputable section
open GlobalTheory GlobalTheory.ChartRing
variable {A : Type*} [CommRing A] (I : Ideal A)
namespace GlobalTheory.ChartRing
theorem _root_.solution (n : ℕ) (f : A⟦X⟧) :
    f ∈ I.comap (constantCoeff (R := A)) ^ n ↔ ∀ i, coeff i f ∈ I ^ (n - i) := by
  constructor
  · induction n generalizing f with
    | zero => simp
    | succ n ih =>
      intro hf
      rw [pow_succ] at hf
      refine Submodule.mul_induction_on hf (fun a ha b hb i => ?_) (fun a b ha hb i => ?_)
      · rw [coeff_mul]
        refine sum_mem fun x hx => ?_
        have hx' := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
        have h1 := ih a ha x.1
        have h2 : coeff x.2 b ∈ I ^ (1 - x.2) := by
          rcases Nat.eq_zero_or_pos x.2 with h | h
          · rw [h]; simpa using hb
          · rw [show 1 - x.2 = 0 by omega]; simp
        have h3 := Ideal.mul_mem_mul h1 h2
        rw [← pow_add] at h3
        exact Ideal.pow_le_pow_right (by omega) h3
      · rw [map_add]; exact add_mem (ha i) (hb i)
  · intro h
    have hX : (X : A⟦X⟧) ∈ I.comap (constantCoeff (R := A)) := by simp
    rw [f.eq_X_pow_mul_shift_add_trunc n]
    refine add_mem (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hX n)) ?_
    rw [trunc_apply, ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
    refine sum_mem fun i hi => ?_
    have hi' : i < n := (Finset.mem_Ico.1 hi).2
    rw [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_monomial,
      monomial_eq_C_mul_X_pow]
    have h1 : C (coeff i f) ∈ I.comap (constantCoeff (R := A)) ^ (n - i) := by
      have := Ideal.mem_map_of_mem (C : A →+* A⟦X⟧) (h i)
      rw [Ideal.map_pow] at this
      refine Ideal.pow_right_mono ?_ _ this
      rw [← map_C_sup_span_X]; exact le_sup_left
    have h2 := Ideal.mul_mem_mul h1 (Ideal.pow_mem_pow hX i)
    rwa [← pow_add, Nat.sub_add_cancel hi'.le] at h2
end GlobalTheory.ChartRing
