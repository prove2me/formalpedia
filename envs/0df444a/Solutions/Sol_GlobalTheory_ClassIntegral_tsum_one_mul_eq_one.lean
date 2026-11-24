-- Prove2me | solution 1 for GlobalTheory.ClassIntegral.tsum_one_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:29:11.106797+00:00
-- url     : https://prove2.me/submissions/e0e010bc-5208-4888-b31e-fe47d30c46b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralFundamentalDomainEqSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory IsDedekindDomain NumberField
open GlobalTheory GlobalTheory.ClassIntegral
variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]
namespace GlobalTheory.ClassIntegral
theorem _root_.solution {α : Type} {m : ENNReal} (h : (∑' _ : α, (1 : ENNReal)) * m = 1) :
    m ≠ ⊤ ∧ m.toReal = (Nat.card α : ℝ)⁻¹ := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at h
  have hN0 : (∑' _ : α, (1 : ENNReal)) ≠ 0 := by intro h0; rw [h0] at h; simp at h
  have hN : (∑' _ : α, (1 : ENNReal)) ≠ ⊤ := by
    intro h0; rw [h0, ENNReal.top_mul hm0] at h; simp at h
  have hm : m ≠ ⊤ := by
    intro h0; rw [h0, ENNReal.mul_top hN0] at h; simp at h
  have : Finite α := by
    by_contra hα
    have : Infinite α := not_finite_iff_infinite.mp hα
    exact hN (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero)
  refine ⟨hm, ?_⟩
  have := Fintype.ofFinite α
  rw [tsum_fintype] at h
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Fintype.card_eq_nat_card] at h
  have h' := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_one] at h'
  exact eq_inv_of_mul_eq_one_right h'
end GlobalTheory.ClassIntegral
