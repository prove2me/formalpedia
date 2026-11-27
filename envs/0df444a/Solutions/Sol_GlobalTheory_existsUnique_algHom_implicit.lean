-- Prove2me | solution 1 for GlobalTheory.existsUnique_algHom_implicit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:37:23.248915+00:00
-- url     : https://prove2.me/submissions/29596c6c-72e9-4530-a845-ea2cb7492a95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_algHom_mem_pow_of_le_order
import Theorems.Thm_GlobalTheory_eq_mvEvalAdic
import Theorems.Thm_GlobalTheory_algHom_sub_mem_of_two_le_order
import Theorems.Thm_GlobalTheory_existsUnique_fixedPoint_of_adic_contraction
import Theorems.Thm_GlobalTheory_sumElim_mem
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.pderivEval_X


attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_C

set_option autoImplicit false
noncomputable section
open GlobalTheory
open MvPowerSeries
variable {A S τ ι : Type*} [CommRing A] [CommRing S] [Algebra A S]
namespace GlobalTheory
theorem _root_.solution [Finite τ] [Finite ι] (J : Ideal S) [IsAdicComplete J S]
    {b : S} (hb : b ∈ nonZeroDivisors S) (hbJ : b ∈ J) (c : ι → A)
    (hc : ∀ i, ∃ e ∈ J, b = algebraMap A S (c i) * e)
    (Q : ι → MvPowerSeries (τ ⊕ ι) A) (hQ : ∀ i, 2 ≤ (Q i).order)
    (u : τ → S) (hu : ∀ k, u k ∈ Ideal.span {b}) :
    ∃! φ : MvPowerSeries (τ ⊕ ι) A →ₐ[A] S, (∀ k, φ (X (Sum.inl k)) = u k) ∧
      (∀ i, φ (X (Sum.inr i)) ∈ Ideal.span {b}) ∧ ∀ i, φ (c i • X (Sum.inr i) + Q i) = 0 := by
  choose e he hbe using hc
  have hB : Ideal.span {b} ≤ J := (Ideal.span_singleton_le_iff_mem _).2 hbJ
  have hpt : ∀ t : ι → S, ∀ v, Sum.elim u (fun i => b * t i) v ∈ Ideal.span {b} := fun t =>
    sumElim_mem hu fun i => Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self b)
  let ev : (ι → S) → (MvPowerSeries (τ ⊕ ι) A →ₐ[A] S) := fun t =>
    mvEvalAdic A J (Sum.elim u fun i => b * t i) fun v => hB (hpt t v)
  have hev : ∀ t v, ev t (X v) = Sum.elim u (fun i => b * t i) v := fun t v => by simp [ev]
  have hr : ∀ t i, ∃ r, ev t (Q i) = b ^ 2 * r := fun t i => by
    have := algHom_mem_pow_of_le_order (ev t) (fun v => hev t v ▸ hpt t v) (n := 2)
      (by exact_mod_cast hQ i)
    rwa [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at this
  choose r hr using hr
  have hcb : ∀ i, algebraMap A S (c i) * b ∈ nonZeroDivisors S := fun i =>
    mul_mem (mul_mem_nonZeroDivisors.1 (hbe i ▸ hb)).1 hb
  have hiff : ∀ t, (fun i => -(e i * r t i)) = t ↔ ∀ i, ev t (c i • X (Sum.inr i) + Q i) = 0 := by
    intro t
    rw [funext_iff]
    refine forall_congr' fun i => ?_
    have : ev t (c i • X (Sum.inr i) + Q i) = algebraMap A S (c i) * b * (t i + e i * r t i) := by
      rw [map_add, map_smul, hev, hr, Algebra.smul_def, Sum.elim_inr]
      linear_combination (b * r t i) * hbe i
    rw [this, mul_left_mem_nonZeroDivisors_eq_zero_iff (hcb i), neg_eq_iff_add_eq_zero, add_comm]
  obtain ⟨t, ht, huniq⟩ := existsUnique_fixedPoint_of_adic_contraction J
    (fun t i => -(e i * r t i)) fun n x y hxy i => by
      have h1 := algHom_sub_mem_of_two_le_order (ev x) (ev y) hB (fun v => hev x v ▸ hpt x v)
        (fun v => hev y v ▸ hpt y v) (n := n) (fun v => by
          rw [hev, hev]
          rcases v with k | i
          · simp
          · simp only [Sum.elim_inr, ← mul_sub]
            exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self b) (hxy i)) (hQ i)
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton_mul] at h1
      obtain ⟨w, hw, hw'⟩ := h1
      rw [hr, hr, ← mul_sub] at hw'
      have h2 : w = r x i - r y i :=
        (mul_cancel_left_mem_nonZeroDivisors (pow_mem hb 2)).1 hw'
      have h3 : -(e i * r x i) - -(e i * r y i) = e i * -w := by rw [h2]; ring
      rw [h3, pow_succ']
      exact Ideal.mul_mem_mul (he i) (neg_mem hw)
  refine ⟨ev t, ⟨fun k => hev t _, fun i => hev t _ ▸ hpt t _, (hiff t).1 ht⟩, ?_⟩
  rintro φ ⟨h1, h2, h3⟩
  choose t' ht' using fun i => Ideal.mem_span_singleton.1 (h2 i)
  have hφ : φ = ev t' := eq_mvEvalAdic J _ _ φ (by
    rintro (k | i)
    exacts [h1 k, ht' i])
  rw [hφ] at h3 ⊢
  rw [huniq t' ((hiff t').2 h3)]
end GlobalTheory
